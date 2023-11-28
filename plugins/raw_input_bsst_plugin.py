import sys
import bsst
import binascii
from typing import Any

from bitcointx import ChainParams
from bitcointx.core.script import CScript

OFFSET_AT = 40


def parse_input_file(env: 'bsst.SymEnvironment', state: dict[str, Any]
                     ) -> 'bsst.ScriptInfo':

    is_binary = state.get('format') == 'binary'
    data: str | bytes
    if env.input_file == '-':
        if is_binary:
            data = sys.stdin.buffer.read()
        else:
            data = sys.stdin.read()
    else:
        with open(env.input_file, 'rb' if is_binary else 'r') as f:
            data = f.read()

    if is_binary:
        assert isinstance(data, bytes)
        bin_data = data
    else:
        assert isinstance(data, str)
        bin_data = binascii.unhexlify(data.strip())

    if len(bin_data) == 0:
        return bsst.ScriptInfo()

    if env.is_elements:
        chain_mode = 'elements'
        import elementstx  # noqa
    else:
        chain_mode = 'bitcoin'

    lines: list[str] = []
    with ChainParams(chain_mode):
        for script_op, script_data, sop_idx in CScript(bin_data).raw_iter():
            pos_str = f'offset: {sop_idx} (0x{sop_idx:X})'
            if script_data is None:
                line = f'{script_op}'
            else:
                line = f"x('{script_data.hex()}')"

            num_spaces = OFFSET_AT - len(line) - 4
            if num_spaces >= 0:
                line = f'{line}{" "*num_spaces} // {pos_str}'
            else:
                line = f'{line}\n{" "*(OFFSET_AT-4)} // {pos_str}'

            lines.append(line)

    bsst.print_as_header('Decoded script:')
    print('\n'.join(lines))
    env.write_line('===============')

    return bsst.parse_script_lines(lines)


def plugin_settings(env: 'bsst.SymEnvironment', settings_str: str,
                    state: dict[str, Any]) -> None:
    if settings_str not in ('hex', 'binary'):
        raise ValueError('unrecognized setting: use either "hex" or "binary"')

    state['format'] = settings_str


# returns a 'state' for the plugin, which will be passed to the hooks
def init(env: bsst.SymEnvironment, bsst_version: str) -> dict[str, Any]:
    env.set_hooks(parse_input_file=parse_input_file,
                  plugin_settings=plugin_settings)
    return {}
