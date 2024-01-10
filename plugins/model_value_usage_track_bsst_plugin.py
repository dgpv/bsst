from types import ModuleType
from typing import Any

if not Any:
    # mock-import bsst - for mypy. we will set bsst global inside init()
    import bsst


def post_finalize(env: 'bsst.SymEnvironment', ctx: 'bsst.ExecContext',  # noqa
                  state: dict[str, Any]) -> None:
    if not env.produce_model_values:
        ctx.add_warning('Signature and preimage tracking is not performed '
                        'for model values, because model values are not '
                        'generated')
        return

    for name, val in ctx.model_value_name_dict.items():
        mvrdict = ctx.model_value_repr_dict.get(name, {})
        results = {
            key: bsst.ModelValueInfo(got_more_values=False)
            for key in state.keys()
        }

        seen_enforcement_pcs: set[int] = set()

        def maybe_enf_dep(sd: 'bsst.SymData') -> str:
            enf_strings: list[str] = []
            for enf in ctx.enforcements:
                if enf.cond.depends_on(sd):
                    seen_enforcement_pcs.add(enf.pc)
                    enf_strings.append(f'{bsst.op_pos_info(enf.pc)}')

            if not enf_strings:
                return ''

            if len(enf_strings) == 1:
                return f' (in enforcement @ {enf_strings[0]})'

            return f' (in enforcements @ {", ".join(enf_strings)})'

        for cso in ctx.sig_check_operations:
            op_txt = f'{cso.op} @ {bsst.op_pos_info(cso.pc)}'
            enfdep = maybe_enf_dep(cso.result)

            if val in cso.signatures:
                results['sig'].value_lines.append(
                    f'Used as signature in {op_txt}{enfdep}')

            if any(val != sig and sig.depends_on(val)
                   for sig in cso.signatures):
                results['sig_dep'].value_lines.append(
                    f'Used as dependency of signature in {op_txt}{enfdep}')

            if val in cso.pubkeys:
                results['pub'].value_lines.append(
                    f'Used as pubkey in {op_txt}{enfdep}')

            if any(val != pub and pub.depends_on(val) for pub in cso.pubkeys):
                results['pub_dep'].value_lines.append(
                    f'Used as dependency of pubkey in {op_txt}{enfdep}')

            if cso.data:
                if val == cso.data:
                    results['sigdata'].value_lines.append(
                        f'Used as data in {op_txt}{enfdep}')
                elif cso.data.depends_on(val):
                    results['sigdata_dep'].value_lines.append(
                        f'Used as dependency of data in {op_txt}{enfdep}')

        for ho in ctx.hash_operations:
            op_txt = f'{ho.op} @ {bsst.op_pos_info(ho.pc)}'
            enfdep = maybe_enf_dep(ho.result)
            if val == ho.data:
                results['preimage'].value_lines.append(
                    f'Used as preimage in {op_txt}{enfdep}')
            elif ho.data.depends_on(val):
                results['preimage_dep'].value_lines.append(
                    f'Used as dependency of preimage in {op_txt}{enfdep}')

        for enf in ctx.enforcements:
            if enf.pc not in seen_enforcement_pcs and enf.cond.depends_on(val):
                results['enf_dep'].value_lines.append(
                    f'Used in enforcement @ {bsst.op_pos_info(enf.pc)}')

        for key, mvrtype in state.items():
            if results[key].value_lines:
                mvrdict[mvrtype] = results[key]

        ctx.model_value_repr_dict[name] = mvrdict


# returns a 'state' for the plugin, which will be passed to the hooks
def init(bsst_module: ModuleType, env: 'bsst.SymEnvironment'
         ) -> dict[str, Any]:

    global bsst
    bsst = bsst_module

    env.set_hooks(post_finalize=post_finalize)

    return {
        'enf_dep': bsst.register_model_value_info_type('ENFORCEMENT_DEP_INFO'),
        'sig': bsst.register_model_value_info_type('SIG_INFO'),
        'sig_dep': bsst.register_model_value_info_type('SIG_DEP_INFO'),
        'pub': bsst.register_model_value_info_type('PUB_INFO'),
        'pub_dep': bsst.register_model_value_info_type('PUB_DEP_INFO'),
        'sigdata': bsst.register_model_value_info_type('SIGDATA_INFO'),
        'sigdata_dep': bsst.register_model_value_info_type('SIGDATA_DEP_INFO'),
        'preimage': bsst.register_model_value_info_type('PREIMAGE_INFO'),
        'preimage_dep': bsst.register_model_value_info_type(
            'PREIMAGE_DEP_INFO')
    }
