#!/usr/bin/env python3
# This program is released under Prosperity Public License 3.0.0
# The text of the license follows:
"""
# The Prosperity Public License 3.0.0

Contributor: Dmitry Petukhov (https://github.com/dgpv), dp@bsst.dev

Source Code: https://github.com/dgpv/bsst

## Purpose

This license allows you to use and share this software for noncommercial
purposes for free and to try this software for commercial purposes for thirty
days.

## Agreement

In order to receive this license, you have to agree to its rules.
Those rules are both obligations under that agreement and conditions to your
license.  Don't do anything with this software that triggers a rule you can't
or won't follow.

## Notices

Make sure everyone who gets a copy of any part of this software from you, with
or without changes, also gets the text of this license and the contributor and
source code lines above.

## Commercial Trial

Limit your use of this software for commercial purposes to a thirty-day trial
period.  If you use this software for work, your company gets one trial period
for all personnel, not one trial per person.

## Contributions Back

Developing feedback, changes, or additions that you contribute back to the
contributor on the terms of a standardized public software license such as
[the Blue Oak Model License 1.0.0](https://blueoakcouncil.org/license/1.0.0),
[the Apache License 2.0](https://www.apache.org/licenses/LICENSE-2.0.html),
[the MIT license](https://spdx.org/licenses/MIT.html), or
[the two-clause BSD license](https://spdx.org/licenses/BSD-2-Clause.html)
doesn't count as use for a commercial purpose.

## Personal Uses

Personal use for research, experiment, and testing for the benefit of public
knowledge, personal study, private entertainment, hobby projects, amateur
pursuits, or religious observance, without any anticipated commercial
application, doesn't count as use for a commercial purpose.

## Noncommercial Organizations

Use by any charitable organization, educational institution, public research
organization, public safety or health organization, environmental protection
organization, or government institution doesn't count as use for a commercial
purpose regardless of the source of funding or obligations resulting from the
funding.

## Defense

Don't make any legal claim against anyone accusing this software, with or
without changes, alone or with other technology, of infringing any patent.

## Copyright

The contributor licenses you to do everything with this software that would
otherwise infringe their copyright in it.

## Patent

The contributor licenses you to do everything with this software that would
otherwise infringe any patents they can license or become able to license.

## Reliability

The contributor can't revoke this license.

## Excuse

You're excused for unknowingly breaking [Notices](#notices) if you take all
practical steps to comply within thirty days of learning you broke the rule.

## No Liability

AS FAR AS THE LAW ALLOWS, THIS SOFTWARE COMES AS IS, WITHOUT ANY WARRANTY
OR CONDITION, AND THE CONTRIBUTOR WON'T BE LIABLE TO ANYONE FOR ANY DAMAGES
RELATED TO THIS SOFTWARE OR THIS LICENSE, UNDER ANY KIND OF LEGAL CLAIM.
"""

# NOTE: while types for values from z3 module are given, because at the
# time of writing the z3 python module did not have typing, effectively
# all z3 types are 'Any'. But when eventually z3 module would become typed,
# we then will be able to check the types without additional effort

# pylama:ignore=E501,E272

import os
import re
import sys
import time
import enum
import types
import struct
import signal
import random
import hashlib
import inspect
import importlib
import importlib.util
import multiprocessing

from typing import TextIO
from multiprocessing.pool import AsyncResult
from copy import deepcopy
from dataclasses import dataclass
from functools import total_ordering
from contextlib import contextmanager

import ctypes
import ctypes.util

from typing import (
    Optional, Union, Callable, Iterable, Sequence, NoReturn, TypeVar, Any,
    Generator, Protocol
)

if not Union:  # always false
    # Fool mypy to think we have imported z3 now.
    # We will try to import it later, as it might not be available
    import z3

ALWAYS_TRUE_WARN_SIGN = '<*>'
LOCAL_ALWAYS_TRUE_SIGN = '{*}'

PLUGIN_FILE_SUFFIX = '_op_plugin.py'
PLUGIN_NAME_PREFIX = 'op_plugin'


class SymEnvironment:

    _nulldummy_flag: Optional[bool]

    @property
    def input_file(self) -> str:
        """The file of the script to analyze. The dash "-" means STDIN
        """
        return self._input_file

    @input_file.setter
    def input_file(self, value: str) -> None:
        self._input_file = value

    @property
    def z3_enabled(self) -> bool:
        """If true, Z3 theorem prover (https://github.com/Z3Prover/z3)
        will be employed to track and enforce constraints on values processed
        by the script. This will significantly improve the thoroughness of
        the analysis.
        If false, the analysis will be fast, but not as thorough, much fewer
        issues may be detected
        """
        return self._z3_enabled

    @z3_enabled.setter
    def z3_enabled(self, value: bool) -> None:
        self._z3_enabled = value

    @property
    def z3_debug(self) -> bool:
        """Enabling this will set `all_z3_assertions_are_tracked_assertions`
        to true, and also shows all triggered tracked assertions as possible
        script failures
        """
        return self._z3_debug

    @z3_debug.setter
    def z3_debug(self, value: bool) -> None:
        self._z3_debug = value

    @property
    def points_of_interest(self) -> set[int | str]:
        """A set of "points" in the script to report the execution state at,
        in addition to the usual information in the report.
        The "point" can be an integer - that means the program counter position
        in the script, or the string "L<num>" where "<num>" is the line number
        in the text of the script
        """
        return self._points_of_interest

    @points_of_interest.setter
    def points_of_interest(self, values: Iterable[str]) -> None:
        result_set: set[int | str] = set()
        for v in values:
            poi_str = v.strip()
            poi: int | str
            if poi_str.isdigit():
                poi = int(poi_str)
            else:
                poi = poi_str

            if isinstance(poi, int) and poi < 0:
                raise ValueError('Negative value is invalid as POI designation')
            elif isinstance(poi, str):
                if not poi.startswith('L'):
                    raise ValueError(
                        'Expected "L" at the start of POI designation')

                if not poi[1:].isdigit():
                    raise ValueError(
                        'Expected number after "L" for POI designation')

                if int(poi[1:]) < 0:
                    raise ValueError(
                        'Negative line value is invalid as POI designation')

            result_set.add(poi)

        self._points_of_interest = result_set

    @property
    def produce_model_values(self) -> bool:
        """Produce 'model values' for fields of transaction, witnesses, and
        the value(s) on the stack after execution has finished (if
        `is_incomplete_script` is true or `cleanstack_flag` is false,
        there may be more than one value on the stack at the end of successful
        execution).

        Model values are the values that, when assigned to said fields, do not
        lead to the script failure. If there is only one such possible value,
        it will be shown with '=' between the name and the value in the report,
        otherwise the separator will be ':'.
        """

        if not self._is_for_usage_message:
            if not self._z3_enabled:
                return False

        return self._produce_model_values

    @produce_model_values.setter
    def produce_model_values(self, value: bool) -> None:
        self._produce_model_values = value

    @property
    def check_always_true_enforcements(self) -> bool:
        """Use Z3 to check enforcements for being 'always true': that is,
        the enforcement condition being false means that no valid execution
        paths exist in the script. Turning this setting off skips that
        detection, which means that the analysis will finish faster.

        When condition is detected as 'always true' it will be marked with
        "<*>" in the report. Always-true conditions may indicate either an
        issue with the script (like, doing `$data DUP EQUALVERIFY` instead of
        `DUP $data EQUALVERIFY`), or an opportunity for optimization, if after
        further analysis it is obvious that other conditions make this
        'always true' enforcement unnecessary. Sometimes the enforcement is
        'always true' only in particular execution path (see
        `mark_path_local_always_true_enforcements`).

        Sometimes 'always true' condition for enforcements can also be detected
        without use of Z3, this settings will not affect these cases.
        """

        if not self._is_for_usage_message:
            if not self._z3_enabled:
                return False

        return self._check_always_true_enforcements

    @check_always_true_enforcements.setter
    def check_always_true_enforcements(self, value: bool) -> None:
        self._check_always_true_enforcements = value

    @property
    def log_progress(self) -> bool:
        """Print progress log as the script is analyzed.
        The progress log lines are sent to STDOUT
        """
        if not self._is_for_usage_message:
            if not self._z3_enabled:
                return False

        return self._log_progress

    @log_progress.setter
    def log_progress(self, value: bool) -> None:
        self._log_progress = value

    @property
    def log_solving_attempts(self) -> bool:
        """In addition to progress log, log info about each solving attempt
        """
        if self._is_for_usage_message:
            return self._log_solving_attempts

        if not self.log_progress:
            return False

        return (self._log_solving_attempts
                or self._log_solving_attempts_to_stderr)

    @log_solving_attempts.setter
    def log_solving_attempts(self, value: bool) -> None:
        self._log_solving_attempts = value

    @property
    def log_solving_attempts_to_stderr(self) -> bool:
        """In addition to progress log, log info about each solving attempt
        to STDERR
        """
        return self._log_solving_attempts_to_stderr

    @log_solving_attempts_to_stderr.setter
    def log_solving_attempts_to_stderr(self, value: bool) -> None:
        self._log_solving_attempts_to_stderr = value

    @property
    def all_z3_assertions_are_tracked_assertions(self) -> bool:
        """Set names for all Z3 assertions generated, making them "tracked".
        This will severely slow down the solving speed. But it may sometimes
        help to find more about the probable cause for 'always true'
        enforcement or for 'only one possible model value'. Automatically
        set to true if `z3_debug` is true
        """
        if not self._is_for_usage_message:
            if self._z3_debug:
                return True

        return self._all_z3_assertions_are_tracked_assertions

    @all_z3_assertions_are_tracked_assertions.setter
    def all_z3_assertions_are_tracked_assertions(self, value: bool) -> None:
        self._all_z3_assertions_are_tracked_assertions = value

    @property
    def use_parallel_solving(self) -> bool:
        """Enable running several solvers in parallel.
        if `parallel_solving_num_processes` is not set, then the number
        of CPUs on the machine will be used. Using parallel solvers is
        likely to speed up the solving. Will be automatically turned off
        if `use_z3_incremental_mode` is true. Parallel solving is only
        available on the platforms that support 'fork' system call for
        'start method' of python multiprocessing module (that means that
        parallel solving is not supported on Windows or MacOS)
        """
        if not self._is_for_usage_message:
            if self._use_z3_incremental_mode:
                return False

        return self._use_parallel_solving

    @use_parallel_solving.setter
    def use_parallel_solving(self, value: bool) -> None:
        self._use_parallel_solving = value

    @property
    def parallel_solving_num_processes(self) -> int:
        """Number of solver processes to run in parallel. If zero, then
        number of available CPU will be used
        """
        if not self._is_for_usage_message:
            if self._use_z3_incremental_mode:
                return 0

        return self._parallel_solving_num_processes

    @parallel_solving_num_processes.setter
    def parallel_solving_num_processes(self, value: int) -> None:
        if value < 1:
            raise ValueError('number of processes must be above 0')

        self._parallel_solving_num_processes = value

    @property
    def solver_timeout_seconds(self) -> int:
        """Timeout in seconds after which the Z3 solving attempt will be
        abandoned, and another attempt will start. Zero means no timeout.

        When solver randomization is enabled (`disable_z3_randomization` is
        false), restarting solver can often help to find solution faster
        """
        if not self._is_for_usage_message:
            if self._use_z3_incremental_mode:
                return 0

        return self._solver_timeout_seconds

    @solver_timeout_seconds.setter
    def solver_timeout_seconds(self, value: int) -> None:
        if value < 0:
            raise ValueError('negative timeout is not valid')

        self._solver_timeout_seconds = value

    @property
    def solver_increasing_timeout_max(self) -> int:
        """Maximum value for solver timeout when increasing timeout is
        employed (via `solver_increasing_timeout_multiplier`)
        """
        return self._solver_increasing_timeout_max

    @solver_increasing_timeout_max.setter
    def solver_increasing_timeout_max(self, value: int) -> None:
        if value < 0:
            raise ValueError('negative timeout is not valid')

        self._solver_increasing_timeout_max = value

    @property
    def solver_increasing_timeout_multiplier(self) -> float:
        """Multiplier to increase the solver timeout after each attempt
        For example, if set to 1.5 and `solver_timeout_seconds` is 10,
        on the second attempt the timeout will be 15 seconds, on third addempt
        22.5 seconds, etc.
        """
        return self._solver_increasing_timeout_multiplier

    @solver_increasing_timeout_multiplier.setter
    def solver_increasing_timeout_multiplier(self, value: float) -> None:
        if value < 1.0:
            raise ValueError('multiplier less than one is not valid')

        self._solver_increasing_timeout_multiplier = value

    @property
    def max_solver_tries(self) -> int:
        """Maximum timer of tries for the solver to get sat or unsat result.
        After this number of tries, the analyzer will exit if
        `exit_on_solver_result_unknown` is true, or will continue analysis.
        In the later case, the analysis might not be correct, because the
        assertions of the unsolved case will be ignored
        """
        return self._max_solver_tries

    @max_solver_tries.setter
    def max_solver_tries(self, value: int) -> None:
        if value < 0:
            raise ValueError('negative timeout is not valid')

        self._max_solver_tries = value

    @property
    def exit_on_solver_result_unknown(self) -> bool:
        """If true, then when the solver did not produce sat or unsat after
        `max_solver_tries` attempts, stop the analysis and exit
        """
        return self._exit_on_solver_result_unknown

    @exit_on_solver_result_unknown.setter
    def exit_on_solver_result_unknown(self, value: bool) -> None:
        self._exit_on_solver_result_unknown = value

    @property
    def use_z3_incremental_mode(self) -> bool:
        """Incremental mode will use weaker solvers (and the solver can run
        for a long time for certain scripts). Non-incremental mode resets the
        solver for each branch, and re-adds all constraints tracked from the
        start of the script, so it will re-check all the constraints for each
        branch. But because Z3 will use stronger solvers in non-incremental
        mode, solving times will likely to actually be faster than in
        incremental mode.  In incremental mode, the randomizations of z3 seeds
        or shuffling of assertions will not be performed, and no repeated
        attempts at finding solutions will be performed on 'unsat' from solver.
        Also no attempts to check if enforcements can be 'always true' will
        be peformed
        """
        return self._use_z3_incremental_mode

    @use_z3_incremental_mode.setter
    def use_z3_incremental_mode(self, value: bool) -> None:
        self._use_z3_incremental_mode = value

    @property
    def disable_error_code_tracking_with_z3(self) -> bool:
        """Disable error code tracking in Z3 assertions. Script failures
        will still be detected as with enabled error code tracking, but
        the failure will be reported as "untracked constraint check failed".
        Disabling error code tracking can speed up solving, at the price
        of losing information about concrete error codes
        """
        return self._disable_error_code_tracking_with_z3

    @disable_error_code_tracking_with_z3.setter
    def disable_error_code_tracking_with_z3(self, value: bool) -> None:
        self._disable_error_code_tracking_with_z3 = value

    @property
    def is_incomplete_script(self) -> bool:
        """If true, final result check will be skipped, and
        `cleanstack_flag` will be set to false
        """
        return self._is_incomplete_script

    @is_incomplete_script.setter
    def is_incomplete_script(self, value: bool) -> None:
        self._is_incomplete_script = value

    @property
    def restrict_data_reference_names(self) -> bool:
        """If false, named references to values in the script via
        specially-formatted comments will be unrestricted, except that
        apostrophe <<'>> is not allowed. Otherwise, these
        names will be checked to be valid python identifiers
        """
        return self._restrict_data_reference_names

    @restrict_data_reference_names.setter
    def restrict_data_reference_names(self, value: bool) -> None:
        self._restrict_data_reference_names = value

    @property
    def assume_no_160bit_hash_collisions(self) -> bool:
        """If true, it is assumed that 160-bit hashes will never collide,
        and the expression "For all x, y, hashfun(x) == hashfun(y) <=> x == y"
        can be deemed true. (NOTE: it is always assumed that 256-bit hash
        functions will never collide)
        """
        return self._assume_no_160bit_hash_collisions

    @assume_no_160bit_hash_collisions.setter
    def assume_no_160bit_hash_collisions(self, value: bool) -> None:
        self._assume_no_160bit_hash_collisions = value

    @property
    def skip_immediately_failed_branches_on(
        self
    ) -> tuple[Union['OpCode', 'ScriptData'], ...]:

        """A script fragment that is expected to fail if top of the stack
        is not True. Will be looked for right after opcodes that leave the
        'success' flag on the stack, like for example ADD64 or MUL64. Any
        enforcement inside that script fragment, that would otherwise be
        registered, will be ignored. Sequences like `ADD64 VERIFY` can
        be viewed as a single opcode that fails on invalid arguments.
        This setting allows the analysis to do just that. If for some reason
        the script uses different sequence of opcodes to detect such failures,
        like for example `1 EQUALVERIFY`, you can set this option with the
        string "1 EQUALVERIFY", or empty string to disable this mechanism.
        """
        return self._skip_immediately_failed_branches_on

    @skip_immediately_failed_branches_on.setter
    def skip_immediately_failed_branches_on(
        self, value: Union[str, tuple[Union['OpCode', 'ScriptData', str], ...]]
    ) -> None:
        """A script fragment that is supposed to check
        """
        if not isinstance(value, str):
            if all(isinstance(v, str) for v in value):
                value = ' '.join(value)  # type: ignore
            else:
                if not all(isinstance(v, (OpCode, ScriptData)) for v in value):
                    raise TypeError('incorrect type of element in supplied tuple')

                # mypy cannot figure out that we checked the types, help it.
                vv: tuple[Union['OpCode', 'ScriptData'], ...] = tuple(value)  # type: ignore
                self._skip_immediately_failed_branches_on = vv
                return

        assert isinstance(value, str)

        with CurrentEnvironment(self.__class__()):
            script_body, _, _ = get_opcodes([value])
            self._skip_immediately_failed_branches_on = script_body

    @property
    def is_miner(self) -> bool:
        """If true, the analysis will assume that only consensus rules apply,
        and policy rules are not (as what would be the case when the script is
        executed by the miner). It is a good idea to analyze both with
        `--is-miner=true` and `--is-miner=false`, to see if the script behavior
        can be different for 'policy rules' vs 'consensus rules'
        """
        return self._is_miner

    @is_miner.setter
    def is_miner(self, value: bool) -> None:
        self._is_miner = value

    @property
    def is_elements(self) -> bool:
        """If true, Elements opcodes and rules will be enabled
        """
        return self._is_elements

    @is_elements.setter
    def is_elements(self, value: bool) -> None:
        self._is_elements = value

    @property
    def sigversion(self) -> 'SigVersion':
        """Rules for script execution. One of: base, witness_v0, tapscript
        """
        return self._sigversion

    @sigversion.setter
    def sigversion(self, value: Union[str, 'SigVersion']) -> None:
        if isinstance(value, str):
            try:
                value = SigVersion[value.upper()]
            except KeyError:
                raise ValueError('unknown sigversion')
        else:
            assert isinstance(value, SigVersion)

        self._sigversion = value

    @property
    def dont_use_tracked_assertions_for_error_codes(self) -> bool:
        """If true, error code detection will use implication instead
        of tracked assertions
        """
        return self._dont_use_tracked_assertions_for_error_codes

    @dont_use_tracked_assertions_for_error_codes.setter
    def dont_use_tracked_assertions_for_error_codes(self, value: bool) -> None:
        self._dont_use_tracked_assertions_for_error_codes = value

    @property
    def disable_z3_randomization(self) -> bool:
        """Disable randomization for Z3 solver.
        Will likely make solving slower
        """
        return self._disable_z3_randomization

    @disable_z3_randomization.setter
    def disable_z3_randomization(self, value: bool) -> None:
        self._disable_z3_randomization = value

    @property
    def do_progressive_z3_checks(self) -> bool:
        """Perform Z3 check after each opcode is symbolically executed.
        When true, analysis time for the whole script will likely be longer,
        but some failures might be detected faster. Also might give
        clearer reasons for paricular failure when the failure is detected
        right after the opcode rather than at the end of execution path
        """
        if not self._is_for_usage_message:
            if self._use_z3_incremental_mode:
                return False

        return self._do_progressive_z3_checks

    @do_progressive_z3_checks.setter
    def do_progressive_z3_checks(self, value: bool) -> None:
        self._do_progressive_z3_checks = value

    @property
    def tag_data_with_position(self) -> bool:
        """If true, each value pushed on the stack will be tagged with
        the value of program counter at the time it was pushed. This will
        make the analysis treat such values as unique within each execution
        path, even if values might actually be the same
        """
        return self._tag_data_with_position

    @tag_data_with_position.setter
    def tag_data_with_position(self, value: bool) -> None:
        self._tag_data_with_position = value

    @property
    def tag_enforcements_with_position(self) -> bool:
        """If true, each enforcement will be tagged with the value of program
        counter at the time it was enforced by the secipt. This will make the
        analysis treat such enforcements as unique within each execution path,
        even if the enforced conditions might be the same
        """
        return self._tag_enforcements_with_position

    @tag_enforcements_with_position.setter
    def tag_enforcements_with_position(self, value: bool) -> None:
        self._tag_enforcements_with_position = value

    @property
    def use_deterministic_arguments_order(self) -> bool:
        """If true, the opcodes where the order of arguments is not important
        will have their arguments sorted according to their canonical
        representation. For example, ADD(3, 1) will be analysed and represented
        as ADD(1, 3)
        """
        return self._use_deterministic_arguments_order

    @use_deterministic_arguments_order.setter
    def use_deterministic_arguments_order(self, value: bool) -> None:
        self._use_deterministic_arguments_order = value

    @property
    def mark_path_local_always_true_enforcements(self) -> bool:
        """If true, the enforcements that are always true only in certain
        execution path, but not in all valid execution paths, will be
        marked with "{*}"
        """

        return self._mark_path_local_always_true_enforcements

    @mark_path_local_always_true_enforcements.setter
    def mark_path_local_always_true_enforcements(self, value: bool) -> None:
        self._mark_path_local_always_true_enforcements = value

    @property
    def discourage_upgradeable_pubkey_type_flag(self) -> bool:
        """SCRIPT_VERIFY_DISCOURAGE_UPGRADEABLE_PUBKEY_TYPE
        """
        if not self._is_for_usage_message:
            if self._is_miner:
                return False

        return self._discourage_upgradeable_pubkey_type_flag

    @discourage_upgradeable_pubkey_type_flag.setter
    def discourage_upgradeable_pubkey_type_flag(self, value: bool) -> None:
        self._discourage_upgradeable_pubkey_type_flag = value

    @property
    def strictenc_flag(self) -> bool:
        """SCRIPT_VERIFY_STRICTENC
        """
        if not self._is_for_usage_message:
            if self._is_miner:
                return False

        return self._strictenc_flag

    @strictenc_flag.setter
    def strictenc_flag(self, value: bool) -> None:
        self._strictenc_flag = value

    @property
    def witness_pubkeytype_flag(self) -> bool:
        """SCRIPT_VERIFY_WITNESS_PUBKEYTYPE
        """
        if not self._is_for_usage_message:
            if self._is_miner:
                return False

        return self._witness_pubkeytype_flag

    @witness_pubkeytype_flag.setter
    def witness_pubkeytype_flag(self, value: bool) -> None:
        self._witness_pubkeytype_flag = value

    @property
    def minimalif_flag(self) -> bool:
        """SCRIPT_VERIFY_MINIMALIF
        """
        if not self._is_for_usage_message:
            if self._sigversion == SigVersion.TAPSCRIPT:
                # MINIMALIF is a consensus rule under tapscript
                return True

            if self._is_miner:
                return False

            if self._sigversion != SigVersion.WITNESS_V0:
                # MINIMALIF is a policy rule segwit, but is not enabled for non-segwit
                return False

        return self._minimalif_flag

    @minimalif_flag.setter
    def minimalif_flag(self, value: bool) -> None:
        self._minimalif_flag = value

    @property
    def minimaldata_flag(self) -> bool:
        """SCRIPT_VERIFY_MINIMALDATA

        If `minimaldata_flag_strict` is false, immediate data values
        are not subjected to checks: `0x01 VERIFY` will not fail
        """
        if not self._is_for_usage_message:
            if self._is_miner:
                return False

            if self._minimaldata_flag_strict:
                return True

        return self._minimaldata_flag

    @minimaldata_flag.setter
    def minimaldata_flag(self, value: bool) -> None:
        self._minimaldata_flag = value

    @property
    def minimaldata_flag_strict(self) -> bool:
        """SCRIPT_VERIFY_MINIMALDATA

        Immediate data values are subjected to checks:
        `0x01 VERIFY` will fail, must use "OP_1" (or just "1") instead

        If true, `minimaldata_flag` is implied to be true
        """
        if not self._is_for_usage_message:
            if self._is_miner:
                return False

        return self._minimaldata_flag_strict

    @minimaldata_flag_strict.setter
    def minimaldata_flag_strict(self, value: bool) -> None:
        self._minimaldata_flag_strict = value

    @property
    def nulldummy_flag(self) -> bool:
        """SCRIPT_VERIFY_NULLDUMMY
        If this flag is not set explicitly, it will be false with
        `--sigversion=base`, and true otherwise
        """
        if not self._is_for_usage_message:
            if self._sigversion != SigVersion.BASE:
                if self._nulldummy_flag is None:
                    return True

        return bool(self._nulldummy_flag)

    @nulldummy_flag.setter
    def nulldummy_flag(self, value: bool) -> None:
        self._nulldummy_flag = value

    @property
    def low_s_flag(self) -> bool:
        """SCRIPT_VERIFY_LOW_S
        Only checked with statically-known signatures
        """
        if not self._is_for_usage_message:
            if self._is_miner:
                return False

        return self._low_s_flag

    @low_s_flag.setter
    def low_s_flag(self, value: bool) -> None:
        self._low_s_flag = value

    @property
    def nullfail_flag(self) -> bool:
        """SCRIPT_VERIFY_NULLFAIL
        """
        if not self._is_for_usage_message:
            if self._is_miner:
                return False

        return self._nullfail_flag

    @nullfail_flag.setter
    def nullfail_flag(self, value: bool) -> None:
        self._nullfail_flag = value

    @property
    def cleanstack_flag(self) -> bool:
        """SCRIPT_VERIFY_CLEANSTACK
        Will be false if `is_incomplete_script` is true
        """
        if not self._is_for_usage_message:
            if self._is_incomplete_script:
                return False

        return self._cleanstack_flag

    @cleanstack_flag.setter
    def cleanstack_flag(self, value: bool) -> None:
        self._cleanstack_flag = value

    @property
    def max_tx_size(self) -> int:
        """Maximum transaction size in bytes (used to limit tx weight as
        max_tx_size*4). Only relevant in Elements mode
        """
        return self._max_tx_size

    @max_tx_size.setter
    def max_tx_size(self, value: int) -> None:
        if value < 0:
            raise ValueError('negative size is not valid')

        self._max_tx_size = value

    @property
    def max_num_inputs(self) -> int:
        """Max possible number of inputs in transaction.

        Default value as per https://bitcoin.stackexchange.com/questions/85752/maximum-number-of-inputs-per-transaction

        Only relevant in Elements mode, and in Elements the inputs are larger.
        This does not take into account the length of the examined script
        either. So the default value should actually be lower, but still, this
        is OK as an upper bound for now. Might adjust default value later.
        """
        return self._max_num_inputs

    @max_num_inputs.setter
    def max_num_inputs(self, value: int) -> None:
        if value < 0:
            raise ValueError('negative number of inputs is not valid')

        self._max_num_inputs = value

    @property
    def max_num_outputs(self) -> int:
        """Max possible number of outputs in transaction.

        Default value is a very rough upper bound based on max possible
        non-seqwit size for transaction and min size of output.
        Might adjust default value later.
        """
        return self._max_num_outputs

    @max_num_outputs.setter
    def max_num_outputs(self, value: int) -> None:
        if value < 0:
            raise ValueError('negative number of outputs is not valid')

        self._max_num_outputs = value

    @property
    def op_plugins(self) -> set[str]:
        """Set of opcode handling plugins to load (paths to python files
        with names ending in '_op_plugin.py')
        """
        return self._op_plugins

    @op_plugins.setter
    def op_plugins(self, value: Iterable[str]) -> None:
        for name in value:
            if not name.endswith(PLUGIN_FILE_SUFFIX):
                raise ValueError(
                    f'plugin file names must end with \'{PLUGIN_FILE_SUFFIX}\'')
            if not os.path.exists(name):
                raise ValueError('plugin file does not exist')

        self._op_plugins = set(value)

    def __init__(self, *, is_for_usage_message: bool = False) -> None:
        self._is_for_usage_message = is_for_usage_message
        self._input_file = '-'
        self._z3_enabled = False
        self._z3_debug = False
        self._points_of_interest = set()
        self._use_z3_incremental_mode = False
        self._use_parallel_solving = True
        self._parallel_solving_num_processes = 0
        self._all_z3_assertions_are_tracked_assertions = False
        self._disable_error_code_tracking_with_z3 = False
        self._is_incomplete_script = False
        self._restrict_data_reference_names = True
        self._assume_no_160bit_hash_collisions = False
        self._skip_immediately_failed_branches_on = (OP_VERIFY,)
        self._sigversion = SigVersion.TAPSCRIPT
        self._is_miner = False
        self._is_elements = False
        self._dont_use_tracked_assertions_for_error_codes = False
        self._solver_timeout_seconds = 5
        self._solver_increasing_timeout_max = 3600*24*365
        self._solver_increasing_timeout_multiplier = 1.5
        self._max_solver_tries = 100
        self._disable_z3_randomization = False
        self._do_progressive_z3_checks = True
        self._log_progress = True
        self._log_solving_attempts = True
        self._log_solving_attempts_to_stderr = False
        self._produce_model_values = True
        self._check_always_true_enforcements = True
        self._exit_on_solver_result_unknown = True
        self._tag_data_with_position = False
        self._use_deterministic_arguments_order = True
        self._tag_enforcements_with_position = True
        self._mark_path_local_always_true_enforcements = True
        self._minimalif_flag = True
        self._minimaldata_flag = True
        self._minimaldata_flag_strict = False
        self._nulldummy_flag = None
        self._discourage_upgradeable_pubkey_type_flag = True
        self._strictenc_flag = True
        self._witness_pubkeytype_flag = True
        self._low_s_flag = True
        self._nullfail_flag = True
        self._cleanstack_flag = True
        self._max_tx_size = 1000000
        self._max_num_inputs = 24386
        self._max_num_outputs = self._max_tx_size // (9+1+33+33)
        self._op_plugins = set()

        self._sym_ec_mul_scalar_fun: Optional['z3.Function'] = None
        self._sym_ec_tweak_add_fun: Optional['z3.Function'] = None
        self._sym_checksig_fun: Optional['z3.Function'] = None
        self._sym_checksigfromstack_fun: Optional['z3.Function'] = None
        self._sym_hashfun: dict[str, 'z3.FuncDeclRef'] = {}
        self._sym_bitfun8: dict[str, 'z3.FuncDeclRef'] = {}
        self._z3_tracked_assertion_lines: dict[str, int] = {}
        self._op_plugin_modules: set[types.ModuleType] = set()

        self.tracked_failure_codes: dict[str, int] = {}
        self.z3_constraints_stack: list[
            tuple[tuple['z3.BoolRef', str,
                        Optional[tuple['SymData', int]]], ...]] = []
        self.z3_current_constraints_frame: list[
            tuple['z3.BoolRef', str, Optional[tuple['SymData', int]]]] = []

        self._root_branch: Optional['Branchpoint'] = None
        self._enabled_opcodes: list['OpCode'] = []
        self._solver: Optional['z3.Solver'] = None
        self._failure_code: Optional['z3.ArithRef'] = None
        self._last_output_chars: dict[TextIO, str] = {}

    def get_solver(self) -> 'z3.Solver':
        if not self.z3_enabled:
            raise ValueError('Z3 is not enabled')

        if self._solver is None:
            self._solver = z3.Solver()

        return self._solver

    def get_failure_code(self) -> Union[int, 'z3.ArithRef']:
        if self.z3_enabled:
            if self._failure_code is None:
                self._failure_code = Int('failure_code')

            return self._failure_code

        return -1

    @classmethod
    def is_option(cls, name: str) -> bool:
        return (not name.startswith('_')
                and name in cls.__dict__.keys()
                and isinstance(getattr(cls, name), property)
                and getattr(cls, name).__doc__)

    def write_out(self, msg: str, f: TextIO) -> None:
        if msg:
            locs = self._last_output_chars.get(f)
            if locs is None:
                locs = '  '

            if len(msg) == 1:
                locs = locs[1] + msg[-1]
            else:
                locs = msg[-2:]

            self._last_output_chars[f] = locs

            f.write(msg)
            f.flush()

    def write(self, msg: str) -> None:
        self.write_out(msg, sys.stdout)

    def write_line(self, msg: str) -> None:
        assert not msg.endswith('\n')
        self.write(f'{msg}\n')

    def ensure_empty_line(self) -> None:
        self.ensure_empty_line_out(sys.stdout)

    def ensure_newline(self) -> None:
        self.ensure_newline_out(sys.stdout)

    def ensure_newline_out(self, f: TextIO) -> None:
        locs = self._last_output_chars.get(f)
        if locs is None or locs[-1] != '\n':
            self.write_out('\n', f)

    def ensure_empty_line_out(self, f: TextIO) -> None:
        locs = self._last_output_chars.get(f)

        if locs is None:
            self.write_out('\n', f)
            return

        if locs == '\n\n':
            return

        if locs[-1] == '\n':
            self.write_out('\n', f)
        else:
            self.write_out('\n\n', f)

    def solving_log_ensure_empty_line(self) -> None:
        if self.log_solving_attempts_to_stderr:
            self.ensure_empty_line_out(sys.stderr)
        elif self.log_solving_attempts:
            self.ensure_empty_line_out(sys.stdout)

    def solving_log_ensure_newline(self) -> None:
        if self.log_solving_attempts_to_stderr:
            self.ensure_newline_out(sys.stderr)
        elif self.log_solving_attempts:
            self.ensure_newline_out(sys.stdout)

    def solving_log_line(self, msg: str) -> None:
        assert not msg.endswith('\n')
        self.solving_log(f'{msg}\n')

    def solving_log(self, msg: str) -> None:
        if self.log_solving_attempts_to_stderr:
            self.write_out(msg, sys.stderr)
        elif self.log_solving_attempts:
            self.write_out(msg, sys.stdout)

    def get_root_branch(self) -> 'Branchpoint':
        if self._root_branch is None:
            with CurrentEnvironment(self):
                self._root_branch = Branchpoint(pc=0, branch_index=0)

        return self._root_branch

    def get_loaded_op_plugins(self) -> set[types.ModuleType]:
        return self._op_plugin_modules

    def get_enabled_opcodes(self) -> tuple['OpCode', ...]:
        mode_ops: set['OpCode']
        if self.is_elements:
            tapscript_ops = set(g_opcodes_for_mode['elements_tapscript']
                                + g_opcodes_for_mode['bitcoin_tapscript'])
            mode_ops = set(g_opcodes_for_mode['elements']
                           + g_opcodes_for_mode['bitcoin'])
        else:
            tapscript_ops = set(g_opcodes_for_mode['bitcoin_tapscript'])
            mode_ops = set(g_opcodes_for_mode['bitcoin'])

        if self.sigversion == SigVersion.TAPSCRIPT:
            mode_ops |= tapscript_ops
            mode_ops -= set(disabled_in_tapscript)

        for pname in self.op_plugins:
            name = op_plugin_name(os.path.basename(pname))
            mode_ops |= set(g_opcodes_for_mode.get(name, []))

        return tuple(mode_ops)

    def load_plugin_modules(self) -> None:
        for ppath in self._op_plugins:
            plugin_filename = os.path.basename(ppath)
            name = op_plugin_name(plugin_filename)
            name = f'{PLUGIN_NAME_PREFIX}_{plugin_filename[:-13]}'
            module_name = f'bsst.{name}'
            if not g_optional_modules_register.get(name):
                spec = importlib.util.spec_from_file_location(module_name, ppath)
                if spec is None:
                    sys.stderr.write(f'cannot load plugin \'{ppath}\': spec_from_file_location failed')
                    sys.exit(-1)

                if spec.loader is None:
                    sys.stderr.write(f'cannot load plugin \'{ppath}\': spec.loader is None')
                    sys.exit(-1)

                plugin_module = importlib.util.module_from_spec(spec)
                if plugin_module is None:
                    sys.stderr.write(f'cannot load plugin \'{ppath}\': module_from_spec failed')
                    sys.exit(-1)

                sys.modules[module_name] = plugin_module
                spec.loader.exec_module(plugin_module)

                with ModeNameForOpcodes(name):
                    plugin_module.init(sys.modules[__name__])

                self._op_plugin_modules.add(plugin_module)

                g_optional_modules_register[name] = True

    def z3_tracked_assertion_line_usagenum(self, lineno_str: str) -> int:
        usageno = self._z3_tracked_assertion_lines.get(lineno_str, 0)
        self._z3_tracked_assertion_lines[lineno_str] = usageno+1
        return usageno

    def get_sym_checksig_fun(self) -> 'z3.FuncDeclRef':
        f = self._sym_checksig_fun
        if f is None:
            f = Function('checksig', IntSeqSortRef(), IntSeqSortRef(), IntSort(), IntSort())
            self._sym_checksig_fun = f

        return f

    def get_sym_checksigfromstack_fun(self) -> 'z3.FuncDeclRef':
        f = self._sym_checksigfromstack_fun
        if f is None:
            f = Function('checksigfromstack',
                         IntSeqSortRef(), IntSeqSortRef(), IntSeqSortRef(), IntSort())
            self._sym_checksigfromstack_fun = f

        return f

    def get_sym_ec_mul_scalar_fun(self) -> 'z3.FuncDeclRef':
        f = self._sym_ec_mul_scalar_fun
        if f is None:
            f = Function('ec_mul_scalar', IntSeqSortRef(), IntSeqSortRef(), IntSeqSortRef())
            self._sym_ec_mul_scalar_fun = f

        return f

    def get_sym_ec_tweak_add_fun(self) -> 'z3.FuncDeclRef':
        f = self._sym_ec_tweak_add_fun
        if f is None:
            f = Function('ec_tweak_add', IntSeqSortRef(), IntSeqSortRef(), IntSeqSortRef())
            self._sym_ec_tweak_add_fun = f

        return f

    def get_sym_hashfun(self, op: 'OpCode') -> tuple['z3.FuncDeclRef', bool]:
        symfun = self._sym_hashfun.get(op.name)
        if symfun is None:
            symfun = Function(f'{op.name}', IntSeqSortRef(), IntSeqSortRef())

            self._sym_hashfun[op.name] = symfun

        if self._assume_no_160bit_hash_collisions:
            collision_possible = False
        else:
            collision_possible = op in (OP_RIPEMD160, OP_SHA1, OP_HASH160)

        return symfun, collision_possible

    def get_sym_bitfun8(self, op: 'OpCode') -> 'z3.FuncDeclRef':

        fun8 = self._sym_bitfun8.get(op.name)

        if fun8 is None:

            def binop(x: 'z3.ArithRef', y: 'z3.ArithRef') -> 'z3.ArithRef':
                if op == OP_AND:
                    return x & y
                elif op == OP_OR:
                    return x | y
                elif op == OP_XOR:
                    return x ^ y
                else:
                    raise AssertionError('unsupported bitfun op')

            fun4 = Function(f'{op.name}4', IntSort(), IntSort(), IntSort())
            for x in range(16):
                for y in range(16):
                    z3add(fun4(x, y) == binop(x, y))

            fun8 = Function(f'{op.name}8', IntSort(), IntSort(), IntSort())

            x = FreshInt('x')
            y = FreshInt('y')
            z3add(z3.ForAll(
                [x, y],
                z3.Implies(z3.And(x >= 0, x < 0x100, y >= 0, y < 0x100),
                           fun8(x, y)
                           == fun4(x / 16, y / 16) * 16 + fun4(x % 16, y % 16))))

            self._sym_bitfun8[op.name] = fun8

        return fun8


MANUAL_TRACKED_ASSERTION_PREFIX = '_line_'
TOTAL_TRACKED_ASSERTION_PREFIX = '_tracked_'

POSSIBLE_TX_VERSIONS = (0, 1, 2)

MAX_PUBKEYS_PER_MULTISIG = 20
MAX_OPS_PER_SCRIPT_SEGWIT_MODE = 201

SEQUENCE_LOCKTIME_DISABLE_FLAG = 1 << 31
SEQUENCE_LOCKTIME_TYPE_FLAG = 1 << 22
SEQUENCE_LOCKTIME_MASK = 0x0000ffff

LOCKTIME_THRESHOLD = 500000000  # Tue Nov  5 00:53:20 1985 UTC

SEQUENCE_FINAL_bytes = bytes.fromhex('ffffffff')

COIN = 100000000
MAX_MONEY = 21000000 * COIN

MAX_STACK_SIZE = 1000
MAX_SCRIPT_ELEMENT_SIZE = 520
MAX_SCRIPT_SIZE = 10000

SCRIPTNUM_DEFAULT_SIZE = 4

_OP_TABLE: dict[str, 'OpCode'] = {}

MAX_SCRIPTNUM_INT = 0x7fffffff
MIN_SCRIPTNUM_INT = -0x7fffffff

SHA256_MAX = 0x1FFFFFFFFFFFFFFF


def op_plugin_name(plugin_filename: str) -> str:
    if not plugin_filename.endswith(PLUGIN_FILE_SUFFIX):
        raise ValueError(f"plugin file name must end with '{PLUGIN_FILE_SUFFIX}'")

    return f'{PLUGIN_NAME_PREFIX}_{plugin_filename[:-13]}'


def IntSeqSortRef() -> 'z3.SeqSortRef':
    if not cur_env().z3_enabled:
        return DummyExpr('SEQ(INT)')

    return z3.SeqSort(z3.IntSort())


def IntSort() -> 'z3.SortRef':
    if not cur_env().z3_enabled:
        return DummyExpr('INT')

    return z3.IntSort()


def Int(v: str) -> 'z3.ArithRef':
    if not cur_env().z3_enabled:
        return DummyExpr('INT', v)

    return z3.Int(v)


def FreshInt(prefix: str) -> 'z3.ArithRef':
    if not cur_env().z3_enabled:
        global g_dummyexpr_counter
        g_dummyexpr_counter += 1
        return DummyExpr('INT', '!{prefix}_{g_dummyexpr_counter}')

    return z3.FreshInt(prefix)


def Const(v: str, sort: Any) -> 'z3.ExprRef':
    if not cur_env().z3_enabled:
        return DummyExpr('CONST', v, sort)

    return z3.Const(v, sort)


def FreshConst(sort: Any, prefix: str) -> 'z3.ExprRef':
    if not cur_env().z3_enabled:
        global g_dummyexpr_counter
        g_dummyexpr_counter += 1
        return DummyExpr('CONST', '!{prefix}_{g_dummyexpr_counter}', sort)

    return z3.FreshConst(sort, prefix)


SCRIPT_FAILURE_PREFIX_SOLVER = ':solver:'

g_optional_modules_register = {'z3': False, 'secp256k1': False}


class SupportsFailureCodeCallbacks(Protocol):
    def get_name_suffix(self) -> str:
        ...


g_current_sym_environment: SymEnvironment | None = None

g_secp256k1_handle: ctypes.CDLL | None = None
g_secp256k1_context: Any = None
g_secp256k1_has_xonly_pubkeys = False

g_is_in_processing = False

g_do_process_data_reference_names = False

g_dummyexpr_counter = 0
g_stack_symdata_index: int | None = None
g_current_exec_context: Optional['ExecContext'] = None
g_current_op: Optional['OpCode'] = None
g_skip_assertion_for_enforcement_condition: Optional[tuple['SymData', int]] = None
g_data_placeholders: dict[str, 'SymData'] = {}

g_check_op_start_time = 0.0

g_mode_name_for_opcodes = ''
g_opcodes_for_mode: dict[str, list['OpCode']] = {}


def maybe_randomize_z3_seeds() -> None:
    env = cur_env()
    if env.z3_enabled and not env.use_z3_incremental_mode \
            and not env.disable_z3_randomization:
        z3.set_param('smt.random_seed', random.randint(0, 2**32-1))
        z3.set_param('sat.random_seed', random.randint(0, 2**32-1))


class DummyExpr:
    def __init__(self, *args: Any) -> None:
        assert not cur_env().z3_enabled
        self._expr = args

    def is_int(self) -> bool:
        return False

    def __add__(self, other: Any) -> 'DummyExpr':
        return self.__class__('add', self._expr, other)

    def __radd__(self, other: Any) -> 'DummyExpr':
        return self.__class__('add', other, self._expr)

    def __mul__(self, other: Any) -> 'DummyExpr':
        return self.__class__('mul', self._expr, other)

    def __rmul__(self, other: Any) -> 'DummyExpr':
        return self.__class__('mul', other, self._expr)

    def __sub__(self, other: Any) -> 'DummyExpr':
        return self.__class__('sub', self._expr, other)

    def __rsub__(self, other: Any) -> 'DummyExpr':
        return self.__class__('sub', other, self._expr)

    def __pow__(self, other: Any) -> 'DummyExpr':
        return self.__class__('pow', self._expr, other)

    def __rpow__(self, other: Any) -> 'DummyExpr':
        return self.__class__('pow', other, self._expr)

    def __div__(self, other: Any) -> 'DummyExpr':
        return self.__class__('div', self._expr, other)

    def __truediv__(self, other: Any) -> 'DummyExpr':
        return self.__div__(other)

    def __rdiv__(self, other: Any) -> 'DummyExpr':
        return self.__class__('div', other, self._expr)

    def __rtruediv__(self, other: Any) -> 'DummyExpr':
        return self.__rdiv__(other)

    def __mod__(self, other: Any) -> 'DummyExpr':
        return self.__class__('mod', self._expr, other)

    def __rmod__(self, other: Any) -> 'DummyExpr':
        return self.__class__('rmod', other, self._expr)

    def __neg__(self) -> 'DummyExpr':
        return self.__class__('neg', self._expr)

    def __pos__(self) -> 'DummyExpr':
        return self.__class__('pos', self._expr)

    def __le__(self, other: Any) -> 'DummyExpr':
        return self.__class__('le', self._expr, other)

    def __lt__(self, other: Any) -> 'DummyExpr':
        return self.__class__('lt', self._expr, other)

    def __gt__(self, other: Any) -> 'DummyExpr':
        return self.__class__('gt', self._expr, other)

    def __ge__(self, other: Any) -> 'DummyExpr':
        return self.__class__('ge', self._expr, other)

    def __eq__(self, other: Any) -> 'DummyExpr':  # type: ignore
        return self.__class__('eq', self._expr, other)

    def __ne__(self, other: Any) -> 'DummyExpr':  # type: ignore
        return self.__class__('ne', self._expr, other)

    def __nonzero__(self) -> 'DummyExpr':
        return self.__bool__()

    def __bool__(self) -> 'DummyExpr':
        return self.__class__('is_true', self._expr)

    def __getitem__(self, arg: Any) -> 'DummyExpr':
        return self.__class__('getitem', self._expr, arg)

    def __call__(self, *args: Any) -> 'DummyExpr':
        return self.__class__('call', *args)

    def __repr__(self) -> str:
        return f'{repr(self._expr)}'


@contextmanager
def VarnamesDisplay(show_assignments: bool = False
                    ) -> Generator[None, None, None]:
    global g_do_process_data_reference_names

    assert not g_do_process_data_reference_names, \
        "no recursive calls to VarnamesDisplay"

    g_do_process_data_reference_names = True
    g_data_reference_names_table.clear()

    env = cur_env()

    try:
        yield
        if g_data_reference_names_table and show_assignments:
            env.ensure_empty_line()
            env.write_line('Data references:')
            env.write_line('----------------')
            data_reference_names_show()
    finally:
        g_do_process_data_reference_names = False
        g_data_reference_names_table.clear()


class FailureCodeDispatcher:

    _tracked_check_codes: dict[str, int]
    _name_prefix: str
    _name_suffix: str | None
    _unique_name_separator = '~'

    def __init__(self, prefix: str) -> None:
        if prefix.startswith('_'):
            raise ValueError('prefix cannot start with "_"')

        if self._unique_name_separator in prefix:
            raise ValueError(
                f'prefix cannot contain "{self._unique_name_separator}"')

        self._tracked_check_codes = {}
        self._name_prefix = prefix
        self._name_suffix = None

    def get_code(self) -> int:
        tfc = cur_env().tracked_failure_codes
        if code := tfc.get(self.name):
            return code

        code = len(tfc) + 1
        tfc[self.name] = code

        return code

    @property
    def name_prefix(self) -> str:
        return self._name_prefix

    @property
    def name(self) -> str:
        if self._name_suffix is None:
            raise ValueError(
                '__call__() was not called, name suffix was not set')
        return f'{self._name_prefix}{self._name_suffix}'

    @property
    def unique_name(self) -> str:
        idx = self._tracked_check_codes.get(self.name, 0)
        self._tracked_check_codes[self.name] = idx + 1
        return f'{self.name}{self._unique_name_separator}{idx}'

    @classmethod
    def strip_unique_name_suffix(cls, name: str) -> str:
        pos = name.rfind(cls._unique_name_separator)
        if pos < 0:
            return name

        if pos == 0:
            raise ValueError('suffix separator at the beginning')

        return name[:pos]

    def __call__(self) -> 'FailureCodeDispatcher':
        self._name_suffix = cur_context().get_name_suffix()
        if self._unique_name_separator in self._name_suffix:
            raise AssertionError(
                f'suffix cannot contain "{self._unique_name_separator}"')
        return self


def parse_failcodes(errstr: str) -> list[tuple[str, int]]:
    info_set: set[tuple[str, int]] = set()
    plen = len(SCRIPT_FAILURE_PREFIX_SOLVER)
    for code in errstr[plen:].split(','):
        code = code.strip()
        if not code:
            continue

        atpos = code.find('@')
        if atpos < 0:
            if code.startswith(f'check_{TOTAL_TRACKED_ASSERTION_PREFIX}_'):
                info_set.add((code, 0))
            else:
                assert code.startswith(
                    f'check_{MANUAL_TRACKED_ASSERTION_PREFIX}_')
                if cur_env().z3_debug:
                    info_set.add((code, 0))
        else:
            lpos = code[atpos+1:].find('L')
            if lpos < 0:
                assert code[atpos+1:atpos+5] in ('END', 'END~')
                pc = len(g_script_body)
            else:
                pc = int(code[atpos+1:atpos+1+lpos])

            info_set.add((code[:atpos], pc))

    info_list = list(info_set)
    info_list.sort(key=lambda info: info[0])
    return info_list


def failcode(name: str) -> FailureCodeDispatcher:
    return FailureCodeDispatcher(name)


err_debug_track_assertion = failcode('DEBUGTRACK')


err_verify = failcode('verify')
err_equalverify = failcode('equalverify')
err_numequalverify = failcode('numequalverify')
err_final_verify = failcode('final_verify')
err_scriptnum_out_of_bounds = failcode('scriptnum_out_of_bounds')
err_scriptnum_encoding_exceeds_datalen = failcode('scriptnum_encoding_exceeds_datalen')
err_le64_wrong_size = failcode('le64_wrong_size')
err_le32_wrong_size = failcode('le32_wrong_size')
err_commitment_wrong_size = failcode('commitment_wrong_size')
err_scriptnum_minimal_encoding = failcode('scriptnum_minimal_encoding')
err_negative_argument = failcode('negative_argument')
err_argument_above_bounds = failcode('argument_above_bounds')
err_invalid_arguments = failcode('invalid_arguments')
err_locktime_type_mismatch = failcode('locktime_type_mismatch')
err_locktime_timelock_in_effect = failcode('locktime_timelock_in_effect')
err_cltv_nsequence_final = failcode('cltv_nsequence_final')
err_nsequence_timelock_in_effect = failcode('nsequence_timelock_in_effect')
err_bad_tx_version = failcode('bad_tx_version')
err_nsequence_type_mismatch = failcode('nsequence_type_mismatch')
err_data_too_long = failcode('data_too_long')
err_length_mismatch = failcode('length_mismatch')
err_invalid_pubkey = failcode('invalid_pubkey')
err_invalid_pubkey_length = failcode('invalid_pubkey_length')
err_invalid_signature_length = failcode('invalid_signature_length')
err_invalid_scalar_length = failcode('invalid_scalar_length')
err_invalid_signature_encoding = failcode('invalid_signature_encoding')
err_signature_low_s = failcode('signature_low_s')
err_signature_bad_hashtype = failcode('signature_bad_hashtype')
err_signature_explicit_sighash_all = failcode('signature_explicit_sighash_all')
err_signature_nullfail = failcode('signature_nullfail')
err_checksigverify = failcode('checksigverify')
err_checkmultisigverify = failcode('checkmultisigverify')
err_checksigfromstackverify = failcode('checksigfromstackverify')
err_ecmultverify = failcode('ecmultverify')
err_tweakverify = failcode('tweakverify')
err_branch_condition_invalid = failcode('branch_condition_invalid')
err_minimalif = failcode('minimalif')
err_out_of_money_range = failcode('out_of_money_range')
err_checkmultisig_bugbyte_zero = failcode('checkmultisig_bugbyte_zero')
err_sha256_context_too_short = failcode('sha256_context_too_short')
err_sha256_context_too_long = failcode('sha256_context_too_long')
err_invalid_sha256_context = failcode('invalid_sha256_context')
err_int64_out_of_bounds = failcode('int64_out_of_bounds')
err_known_args_different_result = failcode('known_args_different_result')
err_known_result_different_args = failcode('known_result_different_args')


class SymDataRType(enum.Enum):
    INT = enum.auto()
    INT64 = enum.auto()
    BYTESEQ = enum.auto()
    LENGTH = enum.auto()


class SigVersion(enum.Enum):
    BASE = 0
    WITNESS_V0 = 1
    # No "TAPROOT": it is a keypath spend, so not relevant to script
    TAPSCRIPT = 3


def IntSeqVal(v: Union[bytes, Union[Sequence[int], Sequence['z3.ArithRef']]]
              ) -> Union['z3.SeqSortRef', bytes]:
    if not cur_env().z3_enabled:
        if isinstance(v, bytes):
            return v

        return DummyExpr('SEQVAL', v)

    if len(v) == 0:
        return z3.Empty(z3.SeqSort(z3.IntSort()))

    if isinstance(v, bytes):
        v = [z3.IntVal(b) for b in v]
    elif isinstance(v[0], int):
        v = [z3.IntVal(intv) for intv in v]

    if len(v) == 1:
        return z3.Unit(v[0])

    tail = Concat(z3.Unit(v[-2]), z3.Unit(v[-1]))

    for elt in v[-3::-1]:
        tail = Concat(z3.Unit(elt), tail)

    return tail


def value_common_repr(v: Union[int, str, bytes, 'IntLE64', None]) -> str:
    if v is None:
        return repr(v)

    if isinstance(v, IntLE64):
        return f'le64({v.as_int()})'
    elif isinstance(v, str):
        return f"'{v}'"
    elif isinstance(v, bytes):
        return f"x('{v.hex()}')"
    elif isinstance(v, int):
        return f'{v}'

    raise AssertionError('unhandled value type {typv(v)}')


def apply_bitmask(sym_v: 'z3.ArithRef', bitmask: int) -> 'z3.ArithRef':

    if bitmask == 0:
        raise ValueError('bitmask cannot be zero')

    exp: z3.ExprRef | None = None
    high = 1
    low = 1
    prev_bit = 0

    for i in range(bitmask.bit_length()+1):  # +1 so that last bit is always 0
        if bitmask & high:
            if prev_bit == 0:
                low = high
            prev_bit = 1
        else:
            if prev_bit == 1:
                new_exp = sym_v % high - sym_v % low
                if exp is None:
                    exp = new_exp
                else:
                    exp = new_exp + exp
            prev_bit = 0

        high <<= 1

    return exp


def _get_byte_bounding_exp(src: 'z3.SeqSortRef', size: int) -> 'z3.BoolRef':
    bounding_chunks = []
    for idx in range(size):
        bounding_chunks.append(src[idx] >= 0)
        bounding_chunks.append(src[idx] < 0x100)

    return And(*bounding_chunks)


def _decode_scriptnum(src: 'z3.SeqSortRef', dst: 'z3.ArithRef', size: int,
                      src_len: 'z3.ArithRef') -> 'z3.BoolRef':
    if size == 0:
        return dst == 0

    v = src[0]
    for idx in range(size-1):
        v += src[idx+1] * 2**(8*(idx+1))

    if size == 1:
        return If(v < 0x80, dst == v, dst == -(v-0x80))

    return If(src_len == size,
              And(_get_byte_bounding_exp(src, size),
                  If(src[size-1] < 0x80,
                     dst == v,
                     dst == -(v - 0x80 * 2**(8*(size-1))))),
              _decode_scriptnum(src, dst, size-1, src_len))


def integer_to_scriptnum(v: int) -> bytes:
    if v == 0:
        return b''

    neg = v < 0
    abs_v = abs(v)

    byte_values: list[int] = []
    while abs_v:
        byte_values.append(abs_v & 0xFF)
        abs_v >>= 8

    if byte_values[-1] & 0x80:
        byte_values.append(0x80 if neg else 0)
    elif neg:
        byte_values[-1] |= 0x80

    return bytes(byte_values)


def scriptnum_to_sym_integer(v_ByteSeq: 'z3.SeqSortRef',
                             v_Int: 'z3.ArithRef',
                             *, max_size: int = 4,
                             ) -> None:
    if max_size > 5:
        raise ValueError(f'unsupported max_size {max_size}')

    env = cur_env()

    if not env.z3_enabled:
        return

    v_Length = Length(v_ByteSeq)

    len_exps: list[z3.BoolRef] = []
    if env.minimaldata_flag:
        len_exps.append((v_Int == 0) == (v_Length == 0))
    else:
        len_exps.append(Implies(v_Length == 0, v_Int == 0))

    for size in range(1, max_size+1):
        bound_exp = And(v_Int > -(2**(size*8-1)),
                        v_Int < (2**(size*8-1)))
        len_exps.append(Implies(v_Length == size, bound_exp))
        len_exps.append(Implies(Not(bound_exp), v_Length > size))

    Check(v_Length <= max_size, err_scriptnum_encoding_exceeds_datalen())
    Check(And(*len_exps))
    Check(Or(v_Int > -(2**((max_size)*8-1)),
             v_Int < (2**((max_size)*8-1))),
          err_scriptnum_out_of_bounds())
    Check(_decode_scriptnum(v_ByteSeq, v_Int, max_size, v_Length))

    if env.minimaldata_flag:
        Check(Or(v_Length == 0,
                 And(v_Length == 1, v_ByteSeq[0] != 0, v_ByteSeq[0] != 0x80),
                 And(v_Length >= 2,
                     Implies(Or(v_ByteSeq[v_Length-1] == 0,
                                v_ByteSeq[v_Length-1] == 0x80),
                             v_ByteSeq[v_Length-2] >= 0x80))),
              err_scriptnum_minimal_encoding())


def _get_le_byteread_exp(bits: int, src: 'z3.SeqSortRef') -> 'z3.ArithRef':
    assert bits % 8 == 0
    size = bits // 8
    assert size > 1

    read_exp = src[0]
    for i in range(1, size):
        read_exp += src[i] * 2**(8*i)

    return read_exp


def le_unsigned_to_integer_exp(bits: int, src: 'z3.SeqSortRef', dst: 'z3.ArithRef',
                               ) -> 'z3.BoolRef':
    size = bits // 8
    return And(_get_byte_bounding_exp(src, size),
               dst == _get_le_byteread_exp(bits, src))


def le_signed_to_integer_exp(bits: int, src: 'z3.SeqSortRef', dst: 'z3.ArithRef',
                             ) -> 'z3.BoolRef':
    size = bits // 8
    rexp = _get_le_byteread_exp(bits, src)
    return And(_get_byte_bounding_exp(src, size),
               If(src[size-1] < 128,
                  dst == rexp,
                  dst == -((2**(8*size)-1) - rexp + 1)))


def le32_signed_to_integer(src: 'z3.SeqSortRef', dst: 'z3.ArithRef') -> None:
    if cur_env().z3_enabled:
        Check(Length(src) == 4, err_le32_wrong_size())
        Check(le_signed_to_integer_exp(32, src, dst))


def le32_unsigned_to_integer(src: 'z3.SeqSortRef', dst: 'z3.ArithRef') -> None:
    if cur_env().z3_enabled:
        Check(Length(src) == 4, err_le32_wrong_size())
        Check(le_unsigned_to_integer_exp(32, src, dst))


def le64_signed_to_integer(src: 'z3.SeqSortRef', dst: 'z3.ArithRef') -> None:
    if cur_env().z3_enabled:
        Check(Length(src) == 8, err_le64_wrong_size())
        Check(le_signed_to_integer_exp(64, src, dst))


def le64_unsigned_to_integer(src: 'z3.SeqSortRef', dst: 'z3.ArithRef') -> None:
    if cur_env().z3_enabled:
        Check(Length(src) == 8, err_le64_wrong_size())
        Check(le_unsigned_to_integer_exp(64, src, dst))


def If(cond: Union[bool, 'z3.BoolRef'],
       true_exp: Union[int, 'z3.ArithRef'],
       false_exp: Union[int, 'z3.ArithRef']
       ) -> Union[int, 'z3.ArithRef']:

    if isinstance(cond, bool):
        if cond:
            return true_exp

        return false_exp

    if not cur_env().z3_enabled:
        return DummyExpr('if', cond, true_exp, false_exp)

    return z3.If(cond, true_exp, false_exp)


def Implies(cond: Union[bool, 'z3.BoolRef'], implied: Union[bool, 'z3.BoolRef']
            ) -> Union[bool, 'z3.BoolRef']:
    if isinstance(cond, bool):
        return (not cond) or implied

    if not cur_env().z3_enabled:
        return DummyExpr('implies', cond, implied)

    return z3.Implies(cond, implied)


def And(*args: Union[bool, 'z3.BoolRef']) -> Union[bool, 'z3.BoolRef']:
    if all(isinstance(a, bool) for a in args):
        return all(args)

    if not cur_env().z3_enabled:
        return DummyExpr('and', *args)

    return z3.And(*args)


def Or(*args: Union[bool, 'z3.BoolRef']) -> Union[bool, 'z3.BoolRef']:
    if all(isinstance(a, bool) for a in args):
        return any(args)

    if not cur_env().z3_enabled:
        return DummyExpr('or', *args)

    return z3.Or(*args)


def Not(v: Union[bool, 'z3.ArithRef']) -> Union[bool, 'z3.ArithRef']:
    if isinstance(v, bool):
        return (not v)

    if not cur_env().z3_enabled:
        return DummyExpr('not', v)

    return z3.Not(v)


def BitMask(v: Union[int, 'z3.ArithRef'], mask: int) -> Union[int, 'z3.ArithRef']:
    if isinstance(v, int):
        if mask == 0:
            raise ValueError('bitmask cannot be zero')
        return v & mask

    if not cur_env().z3_enabled:
        return DummyExpr('bitmask', v, mask)

    return apply_bitmask(v, mask)


def Abs(v: Union[int, 'z3.ArithRef']) -> Union[int, 'z3.ArithRef']:
    if isinstance(v, int):
        return abs(v)

    if not cur_env().z3_enabled:
        return DummyExpr('abs', v)

    return z3.If(v < 0, -v, v)


def Check(cond: Union[bool, 'z3.BoolRef'],
          dispatcher: Optional[FailureCodeDispatcher] = None, *,
          enforcement_condition: Optional['SymData'] = None) -> None:

    if isinstance(cond, bool):
        if not cond:
            if not dispatcher:
                raise ScriptFailure('unexpected condition failure')

            raise ScriptFailure(f'check_{dispatcher.name_prefix}')
    else:
        z3add(cond, dispatcher, enforcement_condition=enforcement_condition)


def Extract(seq: Union['z3.SeqSortRef', bytes],
            start: Union[int, 'z3.ArithRef'],
            length: Union[int, 'z3.ArithRef']) -> 'z3.SeqSortRef':

    if isinstance(seq, bytes) and isinstance(start, int) and \
            isinstance(length, int):
        return seq[start:start+length]

    if not cur_env().z3_enabled:
        return DummyExpr('extract', seq, start, length)

    return z3.Extract(seq, start, length)


def Concat(seq1: Union[bytes, 'z3.SeqSortRef'],
           seq2: Union[bytes, 'z3.SeqSortRef']) -> Union[bytes, 'z3.SeqSortRef']:

    if isinstance(seq1, bytes) and isinstance(seq2, bytes):
        return seq1 + seq2

    if not cur_env().z3_enabled:
        return DummyExpr('concat', seq1, seq2)

    return z3.Concat(seq1, seq2)


def Length(seq: Union['z3.SeqSortRef', bytes]) -> Union[int, 'z3.ArithRef']:
    if isinstance(seq, bytes):
        return len(seq)

    if not cur_env().z3_enabled:
        return DummyExpr('length', seq)

    return z3.Length(seq)


def Function(name: str, *args: 'z3.SortRef') -> 'z3.FuncDeclRef':
    if not cur_env().z3_enabled:
        return DummyExpr('function', name, *args)

    return z3.Function(name, *args)


def get_current_constraints() -> list[tuple['z3.BoolRef', str, Optional[tuple['SymData', int]]]]:
    assertions: list[tuple['z3.BoolRef', str, Optional[tuple['SymData', int]]]] = []
    env = cur_env()
    for frame in env.z3_constraints_stack:
        assertions.extend(frame)

    assertions.extend(env.z3_current_constraints_frame)

    return assertions


def z3_solver_add(exp: 'z3.ExprRef', track_name: str) -> None:
    env = cur_env()
    if env.disable_error_code_tracking_with_z3 and \
            not track_name.startswith('possible_') and \
            not track_name.startswith(MANUAL_TRACKED_ASSERTION_PREFIX) and \
            not track_name.startswith(TOTAL_TRACKED_ASSERTION_PREFIX):
        track_name = ''

    solver = env.get_solver()
    if track_name:
        solver.assert_and_track(exp, f'check_{track_name}')
    else:
        solver.add(exp)


def z3add(exp: 'z3.BoolRef',  # noqa
          dispatcher: Optional[FailureCodeDispatcher] = None, *,
          enforcement_condition: Optional['SymData'] = None,
          _extra_stack_depth: int = 0,
          ) -> None:
    env = cur_env()
    if not env.z3_enabled:
        return

    assert isinstance(exp, z3.BoolRef)

    ecpair: Optional[tuple[SymData, int]] = None
    if enforcement_condition:
        cur_pc = cur_context().pc
        enforcement_condition.mark_as_enforcement_condition(cur_pc)
        ecpair = (enforcement_condition, cur_pc)

    code: int | None = None
    if dispatcher:
        track_name = dispatcher.unique_name
        if env.dont_use_tracked_assertions_for_error_codes:
            # get_code() will update g_tracked_failure_codes
            code = dispatcher.get_code()
    else:
        track_name = ''

    if env.dont_use_tracked_assertions_for_error_codes:
        track_name = ''

    tracked_names: set[str] = set()
    # do not add if the assertion is already in the current stack
    for existing_exp, existing_name, _ in get_current_constraints():
        if exp == existing_exp:
            if not track_name:
                return

            if existing_name:
                # was tracked before, do not add if names match
                tn = FailureCodeDispatcher.strip_unique_name_suffix(track_name)
                en = FailureCodeDispatcher.strip_unique_name_suffix(existing_name)
                if tn == en:
                    return

        if existing_name:
            tracked_names.add(existing_name)

    # Add constraints for failure codes, if any
    for name in (set(env.tracked_failure_codes.keys()) - tracked_names):
        code_exp = (env.get_failure_code() != env.tracked_failure_codes[name])
        assert not isinstance(code_exp, bool), (code_exp, name, None)
        env.z3_current_constraints_frame.append((code_exp, name, None))
        if env.use_z3_incremental_mode:
            z3_solver_add(code_exp, name)

    if (env.all_z3_assertions_are_tracked_assertions and not dispatcher) or \
            dispatcher is err_debug_track_assertion:
        stk = inspect.stack()
        numlines = 3
        lines = ['?' for _ in range(numlines)]
        for i in range(numlines):
            if len(stk) > 2 + i + _extra_stack_depth:
                lines[i] = str(inspect.stack()[2+i+_extra_stack_depth].lineno)

        if dispatcher is err_debug_track_assertion:
            prefix = TOTAL_TRACKED_ASSERTION_PREFIX
        else:
            prefix = MANUAL_TRACKED_ASSERTION_PREFIX

        usageno = env.z3_tracked_assertion_line_usagenum(lines[0])
        track_name = \
            f'{prefix}_{"_".join(lines)}_S{_extra_stack_depth}_{usageno}'

    if env.dont_use_tracked_assertions_for_error_codes and code is not None:
        # code was set but track_name is empty: using code for checks
        exp = z3.Implies(z3.Not(exp), env.get_failure_code() == code)

    assert not isinstance(exp, bool), (exp, track_name, ecpair)
    env.z3_current_constraints_frame.append((exp, track_name, ecpair))

    if env.use_z3_incremental_mode:
        z3_solver_add(z3.simplify(exp), track_name)


def z3_push_context() -> None:
    env = cur_env()
    if env.z3_enabled:
        env.z3_constraints_stack.append(tuple(env.z3_current_constraints_frame))
        env.z3_current_constraints_frame.clear()
        if env.use_z3_incremental_mode:
            env.get_solver().push()


def z3_pop_context() -> None:
    env = cur_env()
    if env.z3_enabled:
        env.z3_current_constraints_frame.clear()
        env.z3_current_constraints_frame.extend(env.z3_constraints_stack.pop())
        if env.use_z3_incremental_mode:
            env.get_solver().pop()


def z3check(  # noqa
    *, force_check: bool = False,
    model_values_to_retrieve: dict[str, tuple[str, SymDataRType]] | None = None
) -> Optional[dict[str, 'ConstrainedValue']]:

    env = cur_env()

    if not env.z3_enabled:
        return None

    if not env.do_progressive_z3_checks and not force_check:
        return None

    solver_timeout_seconds = env.solver_timeout_seconds

    check_fun = _z3check_parallel if env.use_parallel_solving else _z3check

    attempt = 0
    got_sat = False
    while not got_sat:

        attempt += 1
        got_sat, model_values_or_fail_reason = check_fun(
            solver_timeout_seconds, model_values_to_retrieve)

        if got_sat:
            break

        if env.use_z3_incremental_mode:
            break

        if attempt == env.max_solver_tries:
            break

        if env.log_solving_attempts:
            env.solving_log('.')

        solver_timeout_seconds = int(min(
            solver_timeout_seconds*env.solver_increasing_timeout_multiplier,
            env.solver_increasing_timeout_max))

    if not got_sat:
        if env.log_progress:
            env.write(' <UNSOLVED> ')
            if env.exit_on_solver_result_unknown:
                sys.exit(-1)

        assert isinstance(model_values_or_fail_reason, str)
        cur_context().add_warning(
            f'Solver could not find solution: {model_values_or_fail_reason}')

        return None

    assert isinstance(model_values_or_fail_reason, dict)
    return model_values_or_fail_reason


def _z3check(  # noqa
    solver_timeout_seconds: int,
    model_values_to_retrieve: dict[str, tuple[str, SymDataRType]] | None
) -> tuple[bool, dict[str, 'ConstrainedValue'] | str]:

    env = cur_env()
    solver = env.get_solver()

    if not env.use_z3_incremental_mode:
        for exp, tn, ecpair in get_current_constraints():
            assert not isinstance(exp, bool), (exp, tn, ecpair)

        current_assertions = [(z3.simplify(exp), tn, ecpair)
                              for exp, tn, ecpair in get_current_constraints()]
        if not env.disable_z3_randomization:
            random.shuffle(current_assertions)

        # Resetting just before adding all assertions seems to give
        # better performance for some reason. Maybe this is just a false
        # perception, but it won't make things worse anyway
        solver.reset()

        maybe_randomize_z3_seeds()

        z3.set_param('timeout', solver_timeout_seconds*1000)

        skip_ec_set: set[tuple[SymData, int]] = set()
        if g_skip_assertion_for_enforcement_condition:
            cond, pc = g_skip_assertion_for_enforcement_condition
            skip_ec_set = cond.get_enforcement_deps(pc)

        for exp, track_name, ecpair in current_assertions:
            if ecpair and ecpair in skip_ec_set:
                pass
            else:
                z3_solver_add(exp, track_name)

    s_result = solver.check()

    if s_result == z3.sat:
        m = solver.model()
        model_values: dict[str, 'ConstrainedValue'] = {}

        values_dict = {d.name(): m[d] for d in m.decls()}

        for vname, (dname, rtype) in (model_values_to_retrieve or {}).items():

            if dname not in values_dict:
                continue

            ref = values_dict[dname]

            if rtype == SymDataRType.INT:
                assert ref.is_int()
                cv = ConstrainedValue(ref.as_long())
            elif rtype == SymDataRType.INT64:
                assert ref.is_int()
                cv = ConstrainedValue(IntLE64.from_int(ref.as_long()))
            elif rtype == SymDataRType.BYTESEQ:
                assert ref.sort() == IntSeqSortRef()
                seqlen = m.evaluate(Length(ref)).as_long()
                cv = ConstrainedValue(bytes([m.eval(ref[i]).as_long() & 0xFF
                                             for i in range(seqlen)]))
            elif rtype == SymDataRType.LENGTH:
                assert ref.is_int()
                cv = ConstrainedValue(sizes=(ref.as_long(),))
            else:
                raise AssertionError(f'unhandled rtype value {rtype}')

            model_values[vname] = cv

        return True, model_values

    if s_result == z3.unsat:
        unsat_core = solver.unsat_core()
        if not unsat_core:
            raise ScriptFailure('untracked constraint check failed')

        raise ScriptFailure(
            SCRIPT_FAILURE_PREFIX_SOLVER + ' '
            + ', '.join(str(f) for f in unsat_core))

    assert s_result == z3.unknown
    return False, solver.reason_unknown()


def _z3check_parallel(
    solver_timeout_seconds: int,
    model_values_to_retrieve: dict[str, tuple[str, SymDataRType]] | None
) -> tuple['z3.CheckSatResult', dict[str, 'ConstrainedValue'] | str]:

    env = cur_env()
    assert env.use_parallel_solving

    num_processes = env.parallel_solving_num_processes or os.cpu_count()
    assert num_processes

    with multiprocessing.Pool(num_processes) as pool:

        results: list[
            AsyncResult[tuple[bool, dict[str, 'ConstrainedValue'] | str]] | str
        ] = [
            pool.apply_async(_z3check, [solver_timeout_seconds,
                                        model_values_to_retrieve])
            for _ in range(num_processes)
        ]

        pool.close()

        start_time = int(time.monotonic())
        while True:
            for i, r in enumerate(results):
                if isinstance(r, AsyncResult) and r.ready():
                    solver_result = r.get()
                    if not solver_result[0]:
                        assert isinstance(solver_result[1], str)
                        results[i] = solver_result[1]
                    else:
                        assert isinstance(solver_result[1], dict)
                        return solver_result

            if all(isinstance(r, str) for r in results):
                return (False,
                        ', '.join(f'{i}: {r}' for i, r in enumerate(results)))

            time.sleep(0.01)

            now = time.monotonic()
            if solver_timeout_seconds > 0 and \
                    now - start_time >= solver_timeout_seconds:
                return False, 'timeout'


def use_as_script_bool(v: 'SymData') -> Union[int, 'z3.ArithRef']:
    if v.is_static:
        return int(v.as_bool())

    if not cur_env().z3_enabled:
        if v.known_bool_value is not None:
            return int(v.known_bool_value)

        return DummyExpr('as_script_bool', v)

    if v.was_used_as_Int:
        # is already minimal int
        return v.as_Int()

    if v.was_used_as_Int64:
        return If(Or(v.as_Int64() == 0, v.as_Int64() == -0x8000000000000000),
                  0, 1)

    data = v.use_as_ByteSeq()
    data_len = v.Length()

    bigzero = IntSeqVal(b'\x00'*MAX_SCRIPT_ELEMENT_SIZE)
    big_negative_zero = IntSeqVal(b'\x00'*(MAX_SCRIPT_ELEMENT_SIZE-1) + b'\x80')

    return If(Or(z3.Extract(bigzero, MAX_SCRIPT_ELEMENT_SIZE-data_len, data_len)
                 == data,
                 z3.Extract(big_negative_zero, MAX_SCRIPT_ELEMENT_SIZE-data_len, data_len)
                 == data),
              0, 1)


def maybe_enforce_equality_when_z3_disabled(a: 'SymData', b: 'SymData',
                                            is_numeric: bool = False) -> None:
    if cur_env().z3_enabled:
        return

    def getval(v: SymData) -> int | bytes:
        if is_numeric:
            return scriptnum_to_integer(v.as_bytes())

        return v.as_bytes()

    if a.is_static and b.is_static:
        assert getval(a) == getval(b)
    elif a.is_static and not b.is_static:
        b.set_static(getval(a))
    elif not a.is_static and b.is_static:
        a.set_static(getval(b))


def is_cond_possible(  # noqa
    cond: Union[bool, 'z3.BoolRef'], sd: Optional['SymData'] = None,
    *, name: str = '', fail_msg: str = '',
) -> bool:

    env = cur_env()

    z3_push_context()

    if (name or sd) and env.log_progress:
        env.write(f'check {name or sd} ')
        if env.log_solving_attempts_to_stderr:
            env.solving_log(f'  check {name or sd} ')

    if sd:
        sd_failcode = sd.get_failcode_dispatcher('possible')

    try:
        if sd:
            Check(cond, sd_failcode())
        else:
            Check(cond)
    except ScriptFailure:
        if sd and env.log_progress and fail_msg:
            env.ensure_newline()
            env.write_line(f'{fail_msg}, because condition is static')

        z3_pop_context()
        return False

    failcodes: list[tuple[int, str]] = []
    try:
        if sd:
            Check(cond, sd_failcode())
        else:
            Check(cond)

        z3check(force_check=True)
        check_ok = True
    except ScriptFailure as sf:
        ignored_code = ''
        for code, pc in parse_failcodes(str(sf)):
            if code.startswith('check_possible'):
                assert not ignored_code
                ignored_code = code
            else:
                failcodes.append((pc, code))

        if sd and ignored_code:
            assert ignored_code == f'check_{sd_failcode.name_prefix}'

        check_ok = False

    z3_pop_context()

    if sd and env.log_progress:
        maybe_report_elapsed_time()
        env.ensure_newline()
        if not check_ok and fail_msg:
            env.write(fail_msg)
            if failcodes:
                env.write_line(f', probable cause{"s" if len(failcodes) > 1 else ""}:')

                for pc, code in failcodes:
                    if not code.startswith('check_possible'):
                        env.write_line(f"\t{code} @ {op_pos_info(pc)}")
            else:
                env.write('\n')

    return check_ok


def maybe_report_elapsed_time() -> None:
    global g_check_op_start_time

    env = cur_env()

    if env.log_solving_attempts:
        end = time.monotonic()
        env.solving_log(f"... {end-g_check_op_start_time:.02f} seconds")
        g_check_op_start_time = end

        if env.log_solving_attempts_to_stderr:
            env.solving_log("\n")


def get_sym_secp256k1_generator() -> 'z3.SeqSortRef':
    return IntSeqVal(
        bytes.fromhex(
            '0279BE667EF9DCBBAC55A06295CE870B07029BFCDB2DCE28D959F2815B16F81798'))


def CSHA256_Save(csha256: 'CSHA256', r: 'SymData') -> None:
    midstate = csha256.Midstate()
    r.set_static(midstate
                 + struct.pack(b"<q", csha256.bytes_count << 3)
                 + csha256.buf)


def CSHA256_Load(op: 'OpCode', sha256ctx: 'SymData') -> 'CSHA256':
    if len(sha256ctx.as_bytes()) < 40:
        raise ScriptFailure(
            f'{op.name}: sha256 context data too short')

    bits = struct.unpack(b"<q", sha256ctx.as_bytes()[32:40])[0]
    buf_size = (bits >> 3) % 64

    if (bits & 0x07) != 0 or \
            len(sha256ctx.as_bytes()) != 40 + buf_size:
        raise ScriptFailure(
            f'{op.name}: invalid sha256 context')

    csha256 = CSHA256()
    for idx in range(8):
        csha256.s[idx] = struct.unpack(b'>I', sha256ctx.as_bytes()[idx*4:idx*4+4])[0]

    csha256.bytes_count = bits >> 3

    csha256.buf = sha256ctx.as_bytes()[40:]
    return csha256


def CSHA256_SafeWrite(csha256: 'CSHA256', vch: 'SymData') -> None:
    if csha256.bytes_count + len(vch.as_bytes()) > SHA256_MAX:
        raise ScriptFailure('sha256 context: total bytes count too big')

    csha256.Write(vch.as_bytes())


def sym_CSHA256_Load(sha256ctx: 'SymData', bits_load: 'z3.ArithRef',
                     ) -> None:
    ctx_len = sha256ctx.Length()

    Check(ctx_len >= 40, err_sha256_context_too_short())

    Check(ctx_len < 40 + 64, err_sha256_context_too_long())

    le64_unsigned_to_integer(
        Extract(sha256ctx.as_ByteSeq(), 32, 8), bits_load)

    Check(ctx_len == 40 + (bits_load / 8) % 64,
          err_invalid_sha256_context())

    # midstate is initial if less than 64 bytes were processed
    Check(Or(bits_load >= 64,
             Extract(sha256ctx.as_ByteSeq(), 0, 32)
             == IntSeqVal(CSHA256().Midstate())),
          err_invalid_sha256_context())


def is_static_pubkey_valid(pub: bytes) -> bool:
    assert g_secp256k1_handle is not None
    buf = ctypes.create_string_buffer(64)
    is_ok = g_secp256k1_handle.secp256k1_ec_pubkey_parse(
            g_secp256k1_context, buf, pub, len(pub))
    assert is_ok in (1, 0)
    return bool(is_ok)


# NOTE: we could try to verify more of pubkey and signature
# encodings, but this will most likely add a lot of extra load
# on the solver, and it is not clear if chese checks would
# actually be useful. Checking ecdsa signature encoding is
# seems easy though, so we do it.

def add_pubkey_constraints(vchPubKey: 'SymData'
                           ) -> Optional[Union[bool, 'z3.BoolRef']]:
    env = cur_env()

    pub_len = vchPubKey.Length()
    pub = vchPubKey.use_as_ByteSeq()
    if env.witness_pubkeytype_flag and env.sigversion == SigVersion.WITNESS_V0:
        vchPubKey.set_possible_sizes(33, value_name='CPubKey(...)')
        Check(And(pub_len == 33, Or(pub[0] == 2, pub[0] == 3)),
              err_invalid_pubkey())
    else:
        if env.strictenc_flag:
            vchPubKey.set_possible_sizes(33, 65, value_name='CPubKey(...)')
            Check((pub_len == 33) == Or(pub[0] == 2, pub[0] == 3),
                  err_invalid_pubkey())
            Check((pub_len == 65) == (pub[0] == 4),
                  err_invalid_pubkey())

    if vchPubKey.is_static:
        if g_secp256k1_handle is not None:
            return is_static_pubkey_valid(vchPubKey.as_bytes())

    return Or(And(pub_len == 33, Or(pub[0] == 2, pub[0] == 3)),
              And(pub_len == 65, Or(pub[0] == 4, pub[0] == 6, pub[0] == 5)))


def add_xonly_pubkey_constraints(vchPubKey: 'SymData', *,
                                 for_signature_check: bool = True
                                 ) -> Union[bool, 'z3.BoolRef']:

    env = cur_env()

    if env.discourage_upgradeable_pubkey_type_flag or not for_signature_check:

        Check(vchPubKey.Length() == 32,
              err_invalid_pubkey_length())

        vchPubKey.set_possible_sizes(32, value_name='XOnlyPubKey(...)')

        maybe_upgradeable_pub = False
    else:
        Check(vchPubKey.Length() != 0,
              err_invalid_pubkey_length())

        # Miner can have any checksig succeed with non-standard pubkey length,
        # and the signature and its encoding will not be checked at all.
        # Pubkeys are supposed to be hardcoded in the script, and therefore
        # any non-standard pubkey size is expected to be intentional.
        # But we still want to check for this condition, therefore
        # we return it for the caller to use with add_schnorr_sig_constraints()
        maybe_upgradeable_pub = vchPubKey.Length() != 32

    if vchPubKey.is_static and len(vchPubKey.as_bytes()) == 32:
        if g_secp256k1_has_xonly_pubkeys:
            buf = ctypes.create_string_buffer(64)
            assert g_secp256k1_handle is not None
            is_ok = g_secp256k1_handle.secp256k1_xonly_pubkey_parse(
                g_secp256k1_context, buf, vchPubKey.as_bytes())
            assert is_ok in (1, 0)
            if is_ok != 1:
                raise ScriptFailure('invalid pubkey')

    return maybe_upgradeable_pub


def add_ecdsa_sig_constraints(vchSig: Union['SymData', 'z3.ExprRef'], *,  # noqa
                              num_extra_bytes: int = 0
                              ) -> tuple[Union[int, 'z3.ArithRef'], bool]:
    env = cur_env()

    sig: Union['z3.ExprRef', bytes]
    sig_size: Union['z3.ArithRef', int]

    if isinstance(vchSig, SymData):
        if vchSig.is_static:
            sig = vchSig.as_bytes()
            sig_size = len(sig)
        else:
            sig = vchSig.as_ByteSeq()
            sig_size = vchSig.Length()
    else:
        sig = vchSig
        sig_size = Length(sig)

    is_sig_empty = (sig_size - num_extra_bytes == 0)

    if isinstance(is_sig_empty, bool) and is_sig_empty:
        # assume SIGHASH_ALL for empty sig. This will result
        # in this check: `0 == sym_checksig(<empty>, pub, 1)`
        return 1, True

    Check(Or(is_sig_empty,
             And(sig_size >= 9, sig_size <= 73)),
          err_invalid_signature_length())

    lenR = sig[3]

    Check(Or(is_sig_empty, Not(Or(sig[0] != 0x30,
                                  sig[1] != sig_size - 3,
                                  sig[2] != 2,
                                  lenR == 0,
                                  5 + lenR >= sig_size,
                                  sig[4] >= 0x80,
                                  And(lenR > 1,
                                      sig[4] == 0,
                                      sig[5] < 0x80)))),
          err_invalid_signature_encoding())

    lenS = sig[5+lenR]

    Check(Or(is_sig_empty, Not(Or(lenS == 0,
                                  lenR + lenS + 7 != sig_size))),
          err_invalid_signature_encoding())

    Check(Or(is_sig_empty, Not(Or(sig[lenR+4] != 2,
                                  sig[lenR+6] >= 0x80,
                                  And(lenS > 1,
                                      sig[lenR + 6] == 0,
                                      sig[lenR + 7] < 0x80)))),
          err_invalid_signature_encoding())

    is_valid_R = True
    is_valid_S = True
    if isinstance(sig, bytes):
        seq_r = Extract(sig, 4, lenR)
        seq_s = Extract(sig, 6+lenR, lenS)

        if lenR > 32:
            is_valid_R = all(b == 0 for b in seq_r[:lenR-32])

        if lenS > 32:
            is_valid_S = all(b == 0 for b in seq_s[:lenS-32])

        if env.low_s_flag and lenS >= 32:
            Check(is_valid_S, err_signature_low_s())

            max_s = 0x7FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF5D576E7357A4501DDFE92F46681B20A0

            seq_s = seq_s[lenS-32:]
            for i in range(32):
                cmp_b = (max_s >> (8*(31-i))) & 0xFF
                if cmp_b < 0xFF:
                    if seq_s[i] < cmp_b:
                        break

                    Check(seq_s[i] == cmp_b, err_signature_low_s())

    # If is_sig_empty is static and false, the function will return earlier
    # therefore we don't need to check it here, because either sig is
    # not empty, or it is not static, and indexed access to sig is symbolic
    hash_type = sig[sig_size-1]

    if env.strictenc_flag:
        if env.is_elements and env.sigversion == SigVersion.TAPSCRIPT:
            # 0x40 is SIGHASH_RANGEPROOF
            masked_hash_type = hash_type % 0x40
        else:
            # 0x80 is SIGHASH_ANYONECANPAY
            masked_hash_type = hash_type % 0x80

        Check(Or(is_sig_empty,
                 masked_hash_type == 1,   # SIGHASH_ALL
                 masked_hash_type == 2,   # SIGHASH_NONE
                 masked_hash_type == 3),  # SIGHASH_SINGLE
              err_signature_bad_hashtype())

    return hash_type, is_valid_R and is_valid_S


def add_schnorr_sig_constraints(vchSig: 'SymData',
                                is_upgradeable_pub: Union[bool, 'z3.BoolRef']
                                ) -> Union[int, 'z3.ArithRef']:
    env = cur_env()

    Check(Or(is_upgradeable_pub,
             vchSig.Length() == 0,
             vchSig.Length() == 64,
             vchSig.Length() == 65),
          err_invalid_signature_length())

    if not env.z3_enabled and isinstance(is_upgradeable_pub, bool) and \
            not is_upgradeable_pub:
        vchSig.set_possible_sizes(0, 64, 65,
                                  value_name='SchnorrScignature(...)')

    if vchSig.is_static and vchSig.Length() < 65:
        hash_type = 1
    else:
        hash_type = If(vchSig.Length() < 65, 1, vchSig.as_ByteSeq()[64])
        Check(Or(vchSig.Length() < 65, hash_type != 1),
              err_signature_explicit_sighash_all())

    masked_hash_type = hash_type % 0x80

    Check(Or(is_upgradeable_pub,
             Implies(vchSig.Length() == 65,
                     Or(masked_hash_type == 1,     # SIGHASH_ALL,
                        masked_hash_type == 2,     # SIGHASH_NONE
                        masked_hash_type == 3))),  # SIGHASH_SINGLE
          err_signature_bad_hashtype())

    if not env.discourage_upgradeable_pubkey_type_flag:
        ww = SymData(name='warn_upgradeable_pubkey_checksig_always_pass')
        Check(ww.as_Int() == If(is_upgradeable_pub, 1, 0))
        ctx = cur_context()
        ctx.z3_warning_vars.append((ctx.pc, ww))
    else:
        assert not is_upgradeable_pub

    return hash_type


def add_amount_constraints(*, prefix: 'SymData', value: 'SymData',
                           ) -> None:
    # can be 32-byte confidential, or 8-byte explicit value
    prefix.set_possible_values(*(bytes([v]) for v in (1, 8, 9)),
                               value_name='ValuePrefix(...)')
    value.set_possible_sizes(8, 32)

    pfx = prefix.as_ByteSeq()[0]
    Check((pfx == 1) == (value.Length() == 8))
    Check(Or(pfx == 8, pfx == 9) == (value.Length() == 32))
    Check(Implies(pfx == 1,
                  And(le_signed_to_integer_exp(64, value.as_ByteSeq(), value.as_Int64()),
                      value.as_Int64() >= 0, value.as_Int64() <= MAX_MONEY)),
          err_out_of_money_range())


def add_checksig_arg_constraints(vchSig: 'SymData',
                                 vchPubKey: 'SymData',
                                 htype: Union[int, 'z3.ExprRef'],
                                 result: Union[int, 'z3.ExprRef']) -> None:
    env = cur_env()

    if not env.z3_enabled:
        return

    pub = vchPubKey.as_ByteSeq()

    if env.sigversion == SigVersion.TAPSCRIPT:
        sig = If(vchSig.Length() < 65,
                 vchSig.as_ByteSeq(), Extract(vchSig.as_ByteSeq(), 0, 64))
    else:
        sig = If(vchSig.Length() == 0,
                 vchSig.as_ByteSeq(),
                 Extract(vchSig.as_ByteSeq(), 0, vchSig.Length()-1))

    sym_checksig = env.get_sym_checksig_fun()

    Check(result == sym_checksig(sig, pub, htype),
          err_known_args_different_result())

    sym_pub = FreshConst(IntSeqSortRef(), 'pub')
    sym_htype = FreshInt('hashtype')
    Check(z3.ForAll([sym_pub, sym_htype],
                    Implies(And(result == 1,
                                1 == sym_checksig(sig, sym_pub, sym_htype)),
                            And(sym_pub == pub, sym_htype == htype))),
          err_known_result_different_args())


def add_checksigfromstack_arg_constraints(
    vchSig: 'SymData', vchData: 'SymData', vchPubKey: 'SymData',
    result: Union[int, 'z3.ExprRef']
) -> None:

    env = cur_env()

    if not env.z3_enabled:
        return

    sig = vchSig.as_ByteSeq()
    data = vchData.as_ByteSeq()
    pub = vchPubKey.as_ByteSeq()

    sym_checksigfromstack = env.get_sym_checksigfromstack_fun()

    Check(result == sym_checksigfromstack(sig, data, pub),
          err_known_args_different_result())

    sym_pub = FreshConst(IntSeqSortRef(), 'pub')
    sym_data = FreshConst(IntSeqSortRef(), 'data')
    Check(z3.ForAll([sym_pub, sym_data],
                    Implies(And(result == 1,
                                1 == sym_checksigfromstack(sig, sym_data, sym_pub)),
                            And(sym_pub == pub, sym_data == data))),
          err_known_result_different_args())


def add_scriptpubkey_constraints(*, witver: 'SymData', witprog: 'SymData'
                                 ) -> None:

    wv = witver.as_ByteSeq()[0]
    # 0x81 is scriptnum -1
    witver.set_possible_values(*(bytes([v]) for v in (0x81, *range(0, 17))),
                               value_name='WitVer(...)')

    # A witness program is any valid CScript that consists of a 1-byte push opcode
    # followed by a data push between 2 and 40 bytes
    # If spk is not a witness program (witness version will be -1),
    # _SPK_WITPROG will be SHA256 hash of the scriptpubkey
    Check(And(witprog.Length() >= 2, witprog.Length() <= 40))
    Check(Implies(wv == -1, witprog.Length() == 32))
    Check(Implies(witprog.Length() != 32, wv != -1))


def add_op_lshift_constraints(
    src: 'z3.SeqSortRef',
    dst: 'z3.SeqSortRef',
    shift_bits: 'z3.ArithRef',
    shift_bytes: 'z3.ArithRef'
) -> None:

    if not cur_env().z3_enabled:
        return

    def pow2_8bit(nbits: 'z3.ArithRef') -> 'z3.ArithRef':

        def rec_f(nb: int) -> z3.ArithRef:
            if nb == 7:
                return 2**7
            return If(nbits == nb, 2**nb, rec_f(nb+1))

        return rec_f(0)

    idx = FreshInt('idx')
    full_bytes = FreshInt('full_bytes')
    bits = FreshInt('bits')

    Check(full_bytes == shift_bytes)
    Check(bits == shift_bits)

    bit_scale = pow2_8bit(bits)
    bit_coscale = pow2_8bit(8-bits)
    src_len = Length(src)

    prev_byte_shifted = If(Or(idx < full_bytes + 1, bits == 0),
                           0, src[idx-full_bytes-1] / bit_coscale)

    tmpseq = FreshConst(IntSeqSortRef(), 'tmpseq')
    Check(Length(tmpseq) == src_len + full_bytes + 1)

    Check(
        z3.ForAll(idx,
                  Implies(
                      And(idx >= 0, idx <= src_len + full_bytes),
                      And(src[idx] >= 0,
                          src[idx] < 0x100,
                          dst[idx] == If(idx < full_bytes,
                                         0,
                                         If(idx == src_len + full_bytes,
                                            prev_byte_shifted,
                                            ((src[idx - full_bytes]
                                              * bit_scale) % 0x100
                                             + prev_byte_shifted))),
                          tmpseq[idx] == If(idx == 0,
                                            If(dst[0] == 0, 0, -1),
                                            If(dst[idx] == 0,
                                               If(tmpseq[idx-1] < 0,
                                                  tmpseq[idx-1],
                                                  0),
                                               -(idx+1)))))))

    Check(Length(dst) == Abs(tmpseq[src_len + full_bytes]))


@contextmanager
def CurrentEnvironment(env: Optional['SymEnvironment']) -> Generator[None, None, None]:
    global g_current_sym_environment

    prev_env = g_current_sym_environment
    g_current_sym_environment = env
    try:
        yield
    finally:
        g_current_sym_environment = prev_env


@contextmanager
def CurrentExecContext(ctx: Optional['ExecContext']) -> Generator[None, None, None]:
    global g_current_exec_context

    prev_ctx = g_current_exec_context
    g_current_exec_context = ctx
    try:
        yield
    finally:
        g_current_exec_context = prev_ctx


OPCODE_MODES = ('bitcoin', 'bitcoin_tapscript',
                'elements', 'elements_tapscript')


@contextmanager
def ModeNameForOpcodes(name: str) -> Generator[None, None, None]:
    global g_mode_name_for_opcodes

    if name not in OPCODE_MODES and not name.startswith(PLUGIN_NAME_PREFIX):
        raise ValueError('unrecognized mode name for opcodes')

    prev_name = g_mode_name_for_opcodes
    g_mode_name_for_opcodes = name
    try:
        yield
    finally:
        g_mode_name_for_opcodes = prev_name


def cur_context() -> 'ExecContext':
    global g_current_exec_context
    assert g_current_exec_context is not None
    return g_current_exec_context


def cur_env() -> 'SymEnvironment':
    global g_current_sym_environment
    assert g_current_sym_environment is not None
    return g_current_sym_environment


@contextmanager
def CurrentOp(op_or_sd: Optional[Union['OpCode', 'ScriptData']]
              ) -> Generator[None, None, None]:
    global g_current_op
    global g_check_op_start_time

    if isinstance(op_or_sd, OpCode):
        op = op_or_sd
    else:
        op = None

    env = cur_env()

    if env.log_solving_attempts:
        g_check_op_start_time = time.monotonic()
        if env.do_progressive_z3_checks and \
                (op_or_sd is None or isinstance(op_or_sd, OpCode)):
            ctx = cur_context()
            assert (op is None) == (ctx.pc == len(g_script_body))
            if op is not None:
                env.solving_log(f'{op} @ {op_pos_info(ctx.pc)} ')

    prev_op = g_current_op
    g_current_op = op
    try:
        yield
    finally:
        g_current_op = prev_op

        if env.do_progressive_z3_checks and env.log_solving_attempts and \
                isinstance(op_or_sd, OpCode):
            end = time.monotonic()
            env.solving_log(f"... {end-g_check_op_start_time:.02f} seconds\n")


@total_ordering
class OpCode:

    def __init__(self, code: int, name: str) -> None:
        self._code = code
        self._name = name

        assert name not in _OP_TABLE
        _OP_TABLE[name] = self
        assert g_mode_name_for_opcodes

        ops = g_opcodes_for_mode.get(g_mode_name_for_opcodes, [])
        ops.append(self)
        g_opcodes_for_mode[g_mode_name_for_opcodes] = ops

    @property
    def name(self) -> str:
        return self._name

    @property
    def code(self) -> int:
        return self._code

    def __eq__(self, other: Any) -> bool:
        if isinstance(other, ScriptData):
            return False

        if not isinstance(other, OpCode):
            raise ValueError(
                f'{self.__class__.__name__} can only be compared '
                f'for equality with OpCode or ScriptData instance, but '
                f'we got {type(other)}')

        return self._code == other._code

    def __lt__(self, other: Any) -> bool:
        if not isinstance(other, OpCode):
            raise ValueError('can only be compared with OpCode instance')
        return self._code < other._code

    def __int__(self) -> int:
        return self._code

    def __repr__(self) -> str:
        return self.name

    def __str__(self) -> str:
        return self.name

    def __hash__(self) -> int:
        return hash(self._code)


# Bitcoin opcodes

with ModeNameForOpcodes('bitcoin'):
    OP_1NEGATE = OpCode(0x4f, '1NEGATE')
    OP_0 = OpCode(0x00, '0')
    _OP_TABLE['FALSE'] = OP_0
    OP_1 = OpCode(0x51, '1')
    _OP_TABLE['TRUE'] = OP_1
    OP_2 = OpCode(0x52, '2')
    OP_3 = OpCode(0x53, '3')
    OP_4 = OpCode(0x54, '4')
    OP_5 = OpCode(0x55, '5')
    OP_6 = OpCode(0x56, '6')
    OP_7 = OpCode(0x57, '7')
    OP_8 = OpCode(0x58, '8')
    OP_9 = OpCode(0x59, '9')
    OP_10 = OpCode(0x5a, '10')
    OP_11 = OpCode(0x5b, '11')
    OP_12 = OpCode(0x5c, '12')
    OP_13 = OpCode(0x5d, '13')
    OP_14 = OpCode(0x5e, '14')
    OP_15 = OpCode(0x5f, '15')
    OP_16 = OpCode(0x60, '16')
    OP_NOP = OpCode(0x61, 'NOP')
    OP_CODESEPARATOR = OpCode(0xab, 'CODESEPARATOR')
    OP_ADD = OpCode(0x93, 'ADD')
    OP_SUB = OpCode(0x94, 'SUB')
    OP_BOOLAND = OpCode(0x9a, 'BOOLAND')
    OP_BOOLOR = OpCode(0x9b, 'BOOLOR')
    OP_NUMEQUAL = OpCode(0x9c, 'NUMEQUAL')
    OP_NUMEQUALVERIFY = OpCode(0x9d, 'NUMEQUALVERIFY')
    OP_NUMNOTEQUAL = OpCode(0x9e, 'NUMNOTEQUAL')
    OP_LESSTHAN = OpCode(0x9f, 'LESSTHAN')
    OP_GREATERTHAN = OpCode(0xa0, 'GREATERTHAN')
    OP_LESSTHANOREQUAL = OpCode(0xa1, 'LESSTHANOREQUAL')
    OP_GREATERTHANOREQUAL = OpCode(0xa2, 'GREATERTHANOREQUAL')
    OP_MIN = OpCode(0xa3, 'MIN')
    OP_MAX = OpCode(0xa4, 'MAX')
    OP_CHECKLOCKTIMEVERIFY = OpCode(0xb1, 'CHECKLOCKTIMEVERIFY')
    OP_CHECKSEQUENCEVERIFY = OpCode(0xb2, 'CHECKSEQUENCEVERIFY')
    OP_DROP = OpCode(0x75, 'DROP')
    OP_IF = OpCode(0x63, 'IF')
    OP_NOTIF = OpCode(0x64, 'NOTIF')
    OP_ENDIF = OpCode(0x68, 'ENDIF')
    OP_ELSE = OpCode(0x67, 'ELSE')
    OP_VERIFY = OpCode(0x69, 'VERIFY')
    OP_RETURN = OpCode(0x6a, 'RETURN')
    OP_TOALTSTACK = OpCode(0x6b, 'TOALTSTACK')
    OP_FROMALTSTACK = OpCode(0x6c, 'FROMALTSTACK')
    OP_2DROP = OpCode(0x6d, '2DROP')
    OP_2DUP = OpCode(0x6e, '2DUP')
    OP_3DUP = OpCode(0x6f, '3DUP')
    OP_2OVER = OpCode(0x70, '2OVER')
    OP_2ROT = OpCode(0x71, '2ROT')
    OP_2SWAP = OpCode(0x72, '2SWAP')
    OP_IFDUP = OpCode(0x73, 'IFDUP')
    OP_DEPTH = OpCode(0x74, 'DEPTH')
    OP_DUP = OpCode(0x76, 'DUP')
    OP_NIP = OpCode(0x77, 'NIP')
    OP_OVER = OpCode(0x78, 'OVER')
    OP_PICK = OpCode(0x79, 'PICK')
    OP_ROLL = OpCode(0x7a, 'ROLL')
    OP_ROT = OpCode(0x7b, 'ROT')
    OP_SWAP = OpCode(0x7c, 'SWAP')
    OP_TUCK = OpCode(0x7d, 'TUCK')
    OP_SIZE = OpCode(0x82, 'SIZE')
    OP_EQUAL = OpCode(0x87, 'EQUAL')
    OP_EQUALVERIFY = OpCode(0x88, 'EQUALVERIFY')
    OP_1ADD = OpCode(0x8b, '1ADD')
    OP_1SUB = OpCode(0x8c, '1SUB')
    OP_NEGATE = OpCode(0x8f, 'NEGATE')
    OP_ABS = OpCode(0x90, 'ABS')
    OP_NOT = OpCode(0x91, 'NOT')
    OP_0NOTEQUAL = OpCode(0x92, '0NOTEQUAL')
    OP_WITHIN = OpCode(0xa5, 'WITHIN')
    OP_RIPEMD160 = OpCode(0xa6, 'RIPEMD160')
    OP_SHA1 = OpCode(0xa7, 'SHA1')
    OP_SHA256 = OpCode(0xa8, 'SHA256')
    OP_HASH160 = OpCode(0xa9, 'HASH160')
    OP_HASH256 = OpCode(0xaa, 'HASH256')
    OP_CHECKSIG = OpCode(0xac, 'CHECKSIG')
    OP_CHECKSIGVERIFY = OpCode(0xad, 'CHECKSIGVERIFY')
    OP_CHECKMULTISIG = OpCode(0xae, 'CHECKMULTISIG')
    OP_CHECKMULTISIGVERIFY = OpCode(0xaf, 'CHECKMULTISIGVERIFY')

with ModeNameForOpcodes('bitcoin_tapscript'):
    OP_CHECKSIGADD = OpCode(0xba, 'CHECKSIGADD')

disabled_in_tapscript = (OP_CHECKMULTISIG, OP_CHECKMULTISIGVERIFY)

# Elements opcodes

with ModeNameForOpcodes('elements'):
    OP_CAT = OpCode(0x7e, 'CAT')
    OP_SUBSTR = OpCode(0x7f, 'SUBSTR')
    OP_LEFT = OpCode(0x80, 'LEFT')
    OP_RIGHT = OpCode(0x81, 'RIGHT')
    OP_INVERT = OpCode(0x83, 'INVERT')
    OP_AND = OpCode(0x84, 'AND')
    OP_OR = OpCode(0x85, 'OR')
    OP_XOR = OpCode(0x86, 'XOR')
    OP_RSHIFT = OpCode(0x99, 'RSHIFT')
    OP_LSHIFT = OpCode(0x98, 'LSHIFT')
    OP_DETERMINISTICRANDOM = OpCode(0xc0, 'DETERMINISTICRANDOM')
    OP_CHECKSIGFROMSTACK = OpCode(0xc1, 'CHECKSIGFROMSTACK')
    OP_CHECKSIGFROMSTACKVERIFY = OpCode(0xc2, 'CHECKSIGFROMSTACKVERIFY')
    OP_SUBSTR_LAZY = OpCode(0xc3, 'SUBSTR_LAZY')

with ModeNameForOpcodes('elements_tapscript'):
    OP_SHA256INITIALIZE = OpCode(0xc4, 'SHA256INITIALIZE')
    OP_SHA256UPDATE = OpCode(0xc5, 'SHA256UPDATE')
    OP_SHA256FINALIZE = OpCode(0xc6, 'SHA256FINALIZE')
    OP_INSPECTINPUTOUTPOINT = OpCode(0xc7, 'INSPECTINPUTOUTPOINT')
    OP_INSPECTINPUTASSET = OpCode(0xc8, 'INSPECTINPUTASSET')
    OP_INSPECTINPUTVALUE = OpCode(0xc9, 'INSPECTINPUTVALUE')
    OP_INSPECTINPUTSCRIPTPUBKEY = OpCode(0xca, 'INSPECTINPUTSCRIPTPUBKEY')
    OP_INSPECTINPUTSEQUENCE = OpCode(0xcb, 'INSPECTINPUTSEQUENCE')
    OP_INSPECTINPUTISSUANCE = OpCode(0xcc, 'INSPECTINPUTISSUANCE')
    OP_PUSHCURRENTINPUTINDEX = OpCode(0xcd, 'PUSHCURRENTINPUTINDEX')
    OP_INSPECTOUTPUTASSET = OpCode(0xce, 'INSPECTOUTPUTASSET')
    OP_INSPECTOUTPUTVALUE = OpCode(0xcf, 'INSPECTOUTPUTVALUE')
    OP_INSPECTOUTPUTNONCE = OpCode(0xd0, 'INSPECTOUTPUTNONCE')
    OP_INSPECTOUTPUTSCRIPTPUBKEY = OpCode(0xd1, 'INSPECTOUTPUTSCRIPTPUBKEY')
    OP_INSPECTVERSION = OpCode(0xd2, 'INSPECTVERSION')
    OP_INSPECTLOCKTIME = OpCode(0xd3, 'INSPECTLOCKTIME')
    OP_INSPECTNUMINPUTS = OpCode(0xd4, 'INSPECTNUMINPUTS')
    OP_INSPECTNUMOUTPUTS = OpCode(0xd5, 'INSPECTNUMOUTPUTS')
    OP_TXWEIGHT = OpCode(0xd6, 'TXWEIGHT')
    OP_ADD64 = OpCode(0xd7, 'ADD64')
    OP_SUB64 = OpCode(0xd8, 'SUB64')
    OP_MUL64 = OpCode(0xd9, 'MUL64')
    OP_DIV64 = OpCode(0xda, 'DIV64')
    OP_LESSTHAN64 = OpCode(0xdc, 'LESSTHAN64')
    OP_GREATERTHAN64 = OpCode(0xde, 'GREATERTHAN64')
    OP_LESSTHANOREQUAL64 = OpCode(0xdd, 'LESSTHANOREQUAL64')
    OP_GREATERTHANOREQUAL64 = OpCode(0xdf, 'GREATERTHANOREQUAL64')
    OP_NEG64 = OpCode(0xdb, 'NEG64')
    OP_SCRIPTNUMTOLE64 = OpCode(0xe0, 'SCRIPTNUMTOLE64')
    OP_LE64TOSCRIPTNUM = OpCode(0xe1, 'LE64TOSCRIPTNUM')
    OP_LE32TOLE64 = OpCode(0xe2, 'LE32TOLE64')
    OP_ECMULSCALARVERIFY = OpCode(0xe3, 'ECMULSCALARVERIFY')
    OP_TWEAKVERIFY = OpCode(0xe4, 'TWEAKVERIFY')


class ScriptData:
    def __init__(self, name: str | None = None,
                 value: str | bytes | int | None = None,
                 do_check_non_minimal: bool = False):
        if (name is None) and (value is None):
            raise ValueError('name or value must be specified, or both')

        self.name = name
        self.value = value
        self.is_non_minimal = False

        if isinstance(value, (bytes, str)) and do_check_non_minimal:
            if isinstance(value, str):
                data = value.encode('utf-8')
            else:
                data = value

            if len(data) == 0:
                self.is_non_minimal = True  # should have used OP_0
            elif len(data) == 1 and 1 <= data[0] <= 16:
                self.is_non_minimal = True  # should have used OP_1 .. OP_16
            elif len(data) == 1 and data[0] == 0x81:
                self.is_non_minimal = True  # should have used OP_1NEGATE

    def __repr__(self) -> str:
        clsname = self.__class__.__name__
        if self.name is None:
            return f'{clsname}(value={value_common_repr(self.value)})'
        elif self.value is None:
            return f'{clsname}(name={repr(self.name)})'

        return f'{clsname}(name={repr(self.name)}, value={value_common_repr(self.value)})'


g_script_body: tuple[Union[OpCode, 'ScriptData'], ...] = ()
g_line_no_table: list[int] = []
g_var_save_positions: dict[int, str] = {}
g_data_reference_names_table: dict[str, dict[str, tuple['SymData', 'ExecContext']]] = {}
g_seen_named_values: set[str] = set()


class ScriptFailure(Exception):
    ...


def op_pos_repr(pc: int) -> str:
    return str(g_script_body[pc]) if pc < len(g_script_body) else 'FINAL_CHECKS'


def op_pos_info(pc: int, separator: str = ':') -> str:
    if pc >= len(g_script_body):
        assert pc == len(g_script_body)
        return 'END'

    return f'{pc}{separator}L{g_line_no_table[pc]}'


def non_static_value_error(msg: str) -> NoReturn:
    raise ValueError(f'non-static value: {msg}')


def scriptnum_to_integer(v: bytes, max_size: int = SCRIPTNUM_DEFAULT_SIZE
                         ) -> int:
    if len(v) > max_size:
        raise ScriptFailure(
            f'trying to convert {len(v)} bytes to scriptnum, but the '
            f'maximum accepted size is {max_size} bytes')

    if len(v) > 0:
        # If the most-significant-byte - excluding the sign bit - is zero
        # then we're not minimal. Note how this test also rejects the
        # negative-zero encoding, 0x80.
        if v[-1] & 0x7f == 0:
            # One exception: if there's more than one byte and the most
            # significant bit of the second-most-significant-byte is set
            # it would conflict with the sign bit. An example of this case
            # is +-255, which encode to 0xff00 and 0xff80 respectively.
            # (big-endian).
            if len(v) <= 1 or (v[len(v) - 2] & 0x80) == 0:
                msg = "non-minimally encoded script number"
                if cur_env().minimaldata_flag:
                    raise ScriptFailure(msg)
                else:
                    cur_context().add_warning(msg)

    result = 0
    if len(v):
        for i, b in enumerate(v):
            result |= b << 8*i

        if v[-1] & 0x80:
            result -= 0x80 << 8*(len(v)-1)
            return -result

    return result


class Branchpoint:

    _branches: tuple['Branchpoint', ...] = ()
    context: Optional['ExecContext']
    unique_enforcements: set['Enforcement'] | None = None
    seen_enforcements: set['Enforcement'] | None = None

    def __init__(self, *, pc: int,
                 cond: Optional[Union['SymData', tuple['SymData', ...]]] = None,
                 designation: str = '', branch_index: int,
                 parent: Optional['Branchpoint'] = None,
                 context: Optional['ExecContext'] = None) -> None:

        if context:
            context.branchpoint = self

        if cond and not designation:
            raise ValueError('designation must be supplied with cond')

        self.pc = pc
        self.branch_index = branch_index
        self.cond = cond
        self.cond_context = context
        self.designation = designation
        self.parent = parent

        if not context:
            context = ExecContext(branchpoint=self)
            with CurrentExecContext(context):
                context.tx = TransactionFieldValues()

        self.context = context

    def get_valid_branches(self) -> tuple['Branchpoint', ...]:
        return tuple(b for b in self._branches
                     if ((not b.context and b.get_valid_branches())
                         or (b.context and not b.context.failure)))

    @property
    def is_if_branch(self) -> bool:
        if not isinstance(g_script_body[self.pc], OpCode):
            return False

        return g_script_body[self.pc] in (OP_IF, OP_NOTIF)

    def get_path(self, *, skip_failed_branches: bool = True
                 ) -> tuple['Branchpoint', ...]:
        result: list[Branchpoint] = []
        bp = self
        while bp.parent:
            valid_branches = bp.parent.get_valid_branches()
            skip = (len(valid_branches) <= 1
                    and skip_failed_branches
                    and bp.parent.is_if_branch)

            if not skip:
                result.append(bp)

            bp = bp.parent

        return tuple(reversed(result))

    def repr_for_path(self) -> str:
        with CurrentExecContext(self.cond_context):
            cond = f' {self.cond}' if self.cond else ''
        return (f'{g_script_body[self.pc]}{cond} @ {op_pos_info(self.pc)} : '
                f'{self.designation}')

    def get_timeline_strings(self, *, skip_failed_branches: bool = True
                             ) -> list[str]:
        return [bp.repr_for_path() for bp in
                self.get_path(skip_failed_branches=skip_failed_branches)]

    def get_enforcement_path(self, e: "Enforcement") -> tuple['Branchpoint', ...]:
        result: list[Branchpoint] = []
        bp = self
        while bp.parent:
            valid_branches = bp.parent.get_valid_branches()
            if len(valid_branches) > 1:
                if all(e in (bbp.seen_enforcements or ())
                       for bbp in valid_branches if bbp is not bp):
                    pass
                else:
                    result.append(bp)
            elif len(valid_branches) == 1:
                if not bp.parent.is_if_branch:
                    result.append(bp)

            bp = bp.parent

        return tuple(reversed(result))

    def set_branches(self, branches: Iterable['Branchpoint']) -> None:
        self.context = None
        self._branches = tuple(branches)

    def walk_branches(self, cb: Callable[['Branchpoint', int], None], *,
                      is_executing: bool = False,
                      level: int = 0) -> None:

        if self._branches:
            assert self.context is None

            for bp in self._branches:
                bp.walk_branches(cb, level=level+1, is_executing=is_executing)

            if is_executing:
                z3_pop_context()

            had_branches = True
        else:
            had_branches = False

        with CurrentExecContext(self.context):
            cb(self, level)

        # new context(s) were added
        if self._branches and not had_branches:
            assert self.context is None

            for bp in self._branches:
                bp.walk_branches(
                    cb, level=level+1, is_executing=is_executing)

            if is_executing:
                z3_pop_context()

    def walk_contexts(self, cb: Callable[['ExecContext'], None], *,
                      is_executing: bool = False,
                      include_failed: bool = False) -> None:

        def process_context(bp: 'Branchpoint', level: int) -> None:
            if bp.context:
                if not bp.context.failure or include_failed:
                    cb(bp.context)

        self.walk_branches(process_context, is_executing=is_executing)

    def process_always_true_enforcements(self) -> None:
        known_enforcements: dict[int, list[tuple[Enforcement, str]]] = {}

        def collect_sibling_enforcements(ctx: ExecContext) -> None:
            for e in ctx.enforcements:
                if enfs := known_enforcements.get(e.pc):
                    enfs.append((e, e.cond.canonical_repr()))
                else:
                    known_enforcements[e.pc] = [(e, e.cond.canonical_repr())]

        self.walk_contexts(collect_sibling_enforcements)

        for enfs in known_enforcements.values():
            e, cr = enfs[0]
            if all(e is e2
                    or (cr == cr2
                        and (e.is_always_true_in_path
                             == e2.is_always_true_in_path))
                    for e2, cr2 in enfs[1:]):

                for e, _ in enfs:
                    e.is_always_true_global = e.is_always_true_in_path

    def process_unused_values(self
                              ) -> dict[str, tuple['SymData', 'ExecContext']]:
        uvdict: dict[str, tuple['SymData', 'ExecContext']] = {}
        if self.context:
            assert not self.context.failure
            with CurrentExecContext(self.context):
                for uv in self.context.unused_values:
                    uvdict[uv.canonical_repr()] = (uv, self.context)

            return uvdict

        assert self._branches
        valid_branches = self.get_valid_branches()

        if not valid_branches:
            return {}

        uvdict = valid_branches[0].process_unused_values()

        crset = set(uvdict.keys())
        for bp in valid_branches[1:]:
            crset -= set(bp.process_unused_values().keys())

        return {k: uvdict[k] for k in crset}

    def process_unique_enforcements(self) -> None:

        self._process_unique_enforcements()

        def clean_unique_enforcements(bp: Branchpoint,
                                      parent_set: set['Enforcement']) -> None:
            for bbp in bp.get_valid_branches():
                assert bbp.unique_enforcements is not None
                bbp.unique_enforcements -= parent_set
                clean_unique_enforcements(
                    bbp, bbp.unique_enforcements.union(parent_set))

        assert self.unique_enforcements is not None
        clean_unique_enforcements(self, self.unique_enforcements)

    def _process_unique_enforcements(  # noqa
        self
    ) -> Optional[tuple[set['Enforcement'], set['Enforcement']]]:

        if self.context:
            assert not self.context.failure
            eset = set(self.context.enforcements)
            self.seen_enforcements = eset.copy()
            self.unique_enforcements = eset.copy()
            return eset, eset.copy()

        assert self._branches

        valid_branches = self.get_valid_branches()

        enfsets: list[
            tuple['Branchpoint',
                  tuple[set['Enforcement'], set['Enforcement']]]]

        enfsets = []
        for bp in valid_branches:
            with CurrentExecContext(bp.context):
                if es_pair := bp._process_unique_enforcements():
                    enfsets.append((bp, es_pair))

        if not enfsets:
            self.seen_enforcements = set()
            self.unique_enforcements = set()
            return None

        for bp, es_pair in enfsets:
            uenf = es_pair[0].copy()
            for other_bp, other_es_pair in enfsets:
                if bp != other_bp:
                    uenf -= other_es_pair[1]

            bp.unique_enforcements = uenf

        and_set = enfsets[0][1][0]
        or_set = enfsets[0][1][1]

        def recurse_for_aliases(p1: tuple[SymData, ExecContext],
                                p2: tuple[SymData, ExecContext]) -> None:
            d1, c1 = p1
            d2, c2 = p2
            if d1._data_reference != d2._data_reference:
                if d1._data_reference is None:
                    d1._data_reference = d2._data_reference
                elif d2._data_reference is None:
                    d2._data_reference = d1._data_reference
                else:
                    d2._data_reference_aliases.add(d1._data_reference)
                    d1._data_reference_aliases.add(d2._data_reference)

            assert len(d1._args) == len(d2._args)
            for idx in range(len(d1._args)):
                s_arg = d1._args[idx]
                t_arg = d2._args[idx]

                with CurrentExecContext(c1):
                    s_cr = s_arg.canonical_repr()
                with CurrentExecContext(c2):
                    t_cr = t_arg.canonical_repr()
                assert s_cr == t_cr

                recurse_for_aliases((s_arg, c1), (t_arg, c2))

        for _, (a_s, o_s) in enfsets[1:]:
            for e1 in a_s:
                for e2 in and_set:
                    if e1 == e2:
                        recurse_for_aliases((e1.cond, e1.context),
                                            (e2.cond, e2.context))

            for e1 in o_s:
                for e2 in or_set:
                    if e1 == e2:
                        recurse_for_aliases((e1.cond, e1.context),
                                            (e2.cond, e2.context))

            and_set &= a_s
            or_set |= o_s

        self.seen_enforcements = or_set.copy()

        if self.parent is None:
            self.unique_enforcements = and_set.copy()

        return and_set, or_set

    def __str__(self) -> str:
        return f'branch @ {self.pc} : {self.designation}'

    def __hash__(self) -> int:
        return hash(str(self))

    def __eq__(self, other: object) -> bool:
        assert isinstance(other, self.__class__)
        return str(self) == str(other)


class Enforcement:

    def __init__(self, cond: 'SymData', *, pc: int, name: str = '',
                 is_script_bool: bool = False,
                 context: 'ExecContext') -> None:
        self.context = context
        self.cond = cond
        self.pc = pc
        self.name = name
        self.is_script_bool = is_script_bool
        self.is_always_true_in_path = False
        self.is_always_true_global = False

    def clone(self, *, context: 'ExecContext') -> 'Enforcement':
        return Enforcement(self.cond, pc=self.pc, context=context,
                           name=self.name, is_script_bool=self.is_script_bool)

    def _str_informative(self, is_canonical: bool = False) -> str:
        # NOTE: when is_canonical=True, this should give
        # 'canonical representation', so the 'informational decorations'
        # for the returned text must be stable for each run of the program
        with CurrentExecContext(self.context):
            if is_canonical:
                reprtext = self.cond.canonical_repr()
            else:
                reprtext = self.cond.readable_repr(with_name=self.name)

            is_obvious_bool = False
            if cv := self.cond.get_constrained_value():
                is_obvious_bool = (set(cv.possible_values) == set((0, 1)) or
                                   cv.single_value in (1, b'\x01'))

            if self.is_script_bool and not is_obvious_bool:
                reprtext = f'BOOL({reprtext})'

            pos_info_tag = ''
            if cur_env().tag_enforcements_with_position:
                pos_info_tag = f' @ {op_pos_info(self.pc)}'

            alwt_sign = ''
            if self.is_always_true_global:
                alwt_sign = f'{ALWAYS_TRUE_WARN_SIGN} '
            elif (self.is_always_true_in_path and
                  cur_env().mark_path_local_always_true_enforcements):
                alwt_sign = f'{LOCAL_ALWAYS_TRUE_SIGN} '

            return f'{alwt_sign}{reprtext}{pos_info_tag}'

    def __repr__(self) -> str:
        return self._str_informative()

    def __str__(self) -> str:
        return self._str_informative(is_canonical=True)

    def __hash__(self) -> int:
        return hash(str(self))

    def __eq__(self, other: object) -> bool:
        assert isinstance(other, self.__class__)
        return str(self) == str(other)


T_ConstrainedValueValue = Union[int, str, bytes, 'IntLE64']


class ConstrainedValue:
    value_name: str = ''

    def __init__(
        self,
        value: Optional[T_ConstrainedValueValue] = None, *,
        sizes: Iterable[int] = (),
        values: Iterable[T_ConstrainedValueValue] = ()
    ) -> None:

        if value is not None:
            if values:
                raise ValueError(
                    'single value and values parameter are mutually exclusive')
            values = (value,)

        if sizes and values:
            raise ValueError('sizes and values are mutually exclusive')

        self._values = set(values)
        self._sizes = set(sizes)

    @property
    def single_value(self) -> Optional[T_ConstrainedValueValue]:
        if len(self._values) == 1:
            return next(iter((self._values)))

        return None

    @property
    def possible_values(self) -> tuple[T_ConstrainedValueValue, ...]:
        return tuple(self._values)

    @property
    def possible_sizes(self) -> tuple[int, ...]:
        if self._values:
            return tuple(len(self._value_as_bytes(v)) for v in self._values)

        return tuple(self._sizes)

    def set_possible_values(
        self, *_values: Union[T_ConstrainedValueValue, bytearray],
        value_name: str = ''
    ) -> None:
        if not _values:
            raise ValueError('values are not specified')

        vdict: dict[bytes, T_ConstrainedValueValue] = {}
        for v in _values:
            if isinstance(v, bytearray):
                v = bytes(v)

            vdict[self._value_as_bytes(v)] = v

        if self._sizes:
            szset = set(len(bv) for bv in vdict.keys())
            if not (szset & self._sizes):
                raise ScriptFailure(
                    f'trying to set constrained value(s) with size(s) {szset} '
                    f'while possible size(s) {self._sizes} already set')

        bvset = set(vdict.keys())
        if self._values:
            old_bvset = set(self._value_as_bytes(v) for v in self._values)
            new_bvset = bvset & old_bvset
            if not new_bvset:
                raise ScriptFailure(
                    f'trying to set constrained value(s) '
                    f'({b.hex() for b in bvset}) that '
                    f'do not match previously set value(s) '
                    f'({b.hex() for b in old_bvset})')
        else:
            new_bvset = bvset

        self.value_name = value_name
        self._sizes = set()  # sizes will now be taken from value byte-lengths
        self._values = set(vdict[bv] for bv in new_bvset)

    def set_possible_sizes(self, *_sizes: int, value_name: str = '') -> None:
        if not _sizes:
            raise ValueError('sizes are not specified')

        if any(size > MAX_SCRIPT_ELEMENT_SIZE for size in _sizes):
            raise ScriptFailure(f'got size > {MAX_SCRIPT_ELEMENT_SIZE}')

        psizes = set(self.possible_sizes)
        if psizes:
            new_sizes = set(_sizes) & psizes
            if not new_sizes:
                def errmsg(s: str) -> str:
                    return (f'trying to constrain value(s) with size(s) '
                            f'{_sizes} that do not match {s}: {psizes}')

                if self._values:
                    raise ScriptFailure(
                        errmsg('sizes of previously set values'))
                else:
                    raise ScriptFailure(errmsg('previously set sizes'))
        else:
            new_sizes = set(_sizes)

        self.value_name = value_name

        if self._values:
            for v in self._values.copy():
                vb = self._value_as_bytes(v)
                if len(vb) not in new_sizes:
                    self._values.remove(v)

            assert self._values, "at least one value must remain"
        else:
            self._sizes = new_sizes

    def as_bool(self) -> bool:
        v = self.single_value
        if v is None:
            raise ValueError('single value is not available')

        return self._value_as_bool(v)

    def as_scriptnum_int(self, *, max_size: int = 4) -> int:
        v = self.single_value
        if v is None:
            raise ValueError('single value is not available')

        return self._value_as_scriptnum_int(v, max_size=max_size)

    def as_le64(self) -> int:
        v = self.single_value
        if v is None:
            raise ValueError('single value is not available')

        return self._value_as_le64(v)

    def as_bytes(self) -> bytes:
        v = self.single_value
        if v is None:
            raise ValueError('single value is not available')

        return self._value_as_bytes(v)

    def values_as_bool(self) -> tuple[bool, ...]:
        return tuple(self._value_as_bool(v) for v in self._values)

    def values_as_scriptnum_int(self, *, max_size: int = 4) -> tuple[int, ...]:
        if not self._values:
            return ()

        sn_values: list[int] = []
        for v in self._values:
            try:
                sn_values.append(
                    self._value_as_scriptnum_int(v, max_size=max_size))
            except ScriptFailure:
                pass

        if not sn_values:
            raise ScriptFailure(
                'Out of known possible values, no value is a valid ScriptNum')

        return tuple(sn_values)

    def values_as_le64(self) -> tuple[int, ...]:
        if not self._values:
            return ()

        le64_values: list[int] = []
        for v in self._values:
            try:
                le64_values.append(self._value_as_le64(v))
            except ScriptFailure:
                pass

        if not le64_values:
            raise ScriptFailure(
                'Out of known possible values, no value is a valid LE64')

        return tuple(le64_values)

    def values_as_bytes(self) -> tuple[bytes, ...]:
        return tuple(self._value_as_bytes(v) for v in self._values)

    def _value_as_bool(self, v: T_ConstrainedValueValue) -> bool:
        vb = self._value_as_bytes(v)
        for i, b in enumerate(vb):
            if b:
                is_negative_zero = (b == 0x80 and (i == len(vb)-1))
                return not is_negative_zero

        return False

    def _value_as_scriptnum_int(self, v: T_ConstrainedValueValue, *,
                                max_size: int = 4) -> int:
        r: int
        if isinstance(v, int):
            max_value = 2**(8*max_size-1)-1
            min_value = -max_value
            if v > max_value:
                raise ScriptFailure(f'scriptnum value above {max_value}')
            if v < min_value:
                raise ScriptFailure(f'scriptnum value below {min_value}')
            r = v
        elif isinstance(v, IntLE64):
            raise ScriptFailure('LE64 cannot be converted to scriptnum')
        elif isinstance(v, str):
            r = scriptnum_to_integer(v.encode('utf-8'), max_size=max_size)
        elif isinstance(v, bytes):
            r = scriptnum_to_integer(v, max_size=max_size)
        else:
            raise AssertionError('unhandled value type')

        return r

    def _value_as_le64(self, v: T_ConstrainedValueValue) -> int:
        if isinstance(v, int):
            vb = struct.pack(b'<q', v)
        else:
            vb = self._value_as_bytes(v)

        return IntLE64(vb).as_int()

    def _value_as_bytes(self, v: Union[int, str, bytes, 'IntLE64']) -> bytes:
        if isinstance(v, int):
            return integer_to_scriptnum(v)
        elif isinstance(v, bytes):
            return v
        elif isinstance(v, str):
            return v.encode('utf-8')

        raise AssertionError(f'unhandled value type {type(v)}')

    def canonical_repr(self) -> str:
        v = self.single_value
        if v is None:
            # canonical_repr will be used to compare symbolic values,
            # therefore it can only be available if static value is set
            raise ValueError('single value is not available')

        return value_common_repr(v)

    def __repr__(self) -> str:
        if self.single_value is not None:
            return self.canonical_repr()

        if self._values:
            vstring = ", ".join(value_common_repr(v) for v in self._values)
            return f'one_of({vstring})'

        psizes = self.possible_sizes
        if not psizes:
            raise ValueError(
                'non-initialized ConstrainedValue cannot be represented')

        return (f'value_of_size{"s" if len(psizes) > 1 else ""}'
                f'({", ".join(str(s) for s in psizes)})')


class TxValuesDict:

    _values: dict[int, 'SymData']

    def __init__(self, name: str, tx: 'TransactionFieldValues') -> None:
        self.tx = tx
        self._name = name
        self._values = {}
        self._sym_fun = Function(name, IntSort(), IntSeqSortRef())

    def get_known(self, key: Union[int, 'z3.ArithSortRef']) -> Optional['SymData']:
        if isinstance(key, int):
            return self._values.get(key)

        return None

    def values(self) -> list['SymData']:
        return list(self._values.values())

    def __getitem__(self, key: Union[int, 'z3.ArithSortRef']
                    ) -> Optional[Union['SymData', 'z3.ExprRef']]:
        if isinstance(key, int):
            if v := self._values.get(key):
                return v

        return self._sym_fun(key)

    def __setitem__(self, key: Union[int, 'z3.ArithSortRef'], value: 'SymData') -> None:
        if isinstance(key, int):
            if key in self._values:
                raise ValueError(f'value already set for {self._name}[{key}]')

            self._values[key] = value

        if not cur_env().z3_enabled:
            return

        sortref = self._sym_fun.range()
        assert isinstance(sortref, z3.SeqSortRef)
        z3add(self._sym_fun(key) == value.use_as_ByteSeq())

    def as_ref(self, key: Union[int, 'z3.ArithSortRef']) -> Union['z3.ExprRef', bytes]:
        value = self[key]
        if not isinstance(value, SymData):
            if cur_env().z3_enabled:
                assert isinstance(value, z3.ExprRef)
            else:
                assert isinstance(value, DummyExpr)

            return value

        return value.as_ByteSeq()

    def clone_to(self, tx: 'TransactionFieldValues') -> 'TxValuesDict':
        inst = self.__class__(self._name, tx)
        inst._values = self._values.copy()
        inst._sym_fun = self._sym_fun
        return inst


class TransactionFieldValues:
    _num_inputs: Optional['SymData'] = None
    _num_outputs: Optional['SymData'] = None
    _nVersion: Optional['SymData'] = None
    _nLockTime: Optional['SymData'] = None
    _weight: Optional['SymData'] = None
    _current_input_index: Optional['SymData'] = None

    def __init__(self) -> None:
        self.nSequence = TxValuesDict('nSequence', self)
        self.input_prevout_n = TxValuesDict('input_prevout_n', self)
        self.input_outpoint_flag = TxValuesDict('input_outpoint_flag', self)
        self.input_outpoint_hash = TxValuesDict('input_outpoint_hash', self)
        self.input_asset = TxValuesDict('input_asset', self)
        self.input_asset_prefix = TxValuesDict('input_asset_prefix', self)
        self.input_value = TxValuesDict('input_value', self)
        self.input_value_prefix = TxValuesDict('input_value_prefix', self)
        self.input_scriptpubkey_witprog = TxValuesDict('input_scriptpubkey_witprog', self)
        self.input_scriptpubkey_witver = TxValuesDict('input_scriptpubkey_witver', self)
        self.issuance_inflationkeys = TxValuesDict('issuance_inflationkeys', self)
        self.issuance_inflationkeys_prefix = TxValuesDict('issuance_inflationkeys_prefix', self)
        self.issuance_amount = TxValuesDict('issuance_amount', self)
        self.issuance_amount_prefix = TxValuesDict('issuance_amount_prefix', self)
        self.issuance_asset_entropy = TxValuesDict('issuance_asset_entropy', self)
        self.issuance_asset_blinding_nonce = TxValuesDict('issuance_asset_blinding_nonce', self)

        self.output_scriptpubkey_witprog = TxValuesDict('output_scriptpubkey_witprog', self)
        self.output_scriptpubkey_witver = TxValuesDict('output_scriptpubkey_witver', self)
        self.output_value = TxValuesDict('output_value', self)
        self.output_value_prefix = TxValuesDict('output_value_prefix', self)
        self.output_asset = TxValuesDict('output_asset', self)
        self.output_asset_prefix = TxValuesDict('output_asset_prefix', self)
        self.output_nonce = TxValuesDict('output_nonce', self)

    @property
    def num_inputs(self) -> 'SymData':
        if self._num_inputs is None:
            self._num_inputs = SymData(name='tx_num_inputs')
            self._num_inputs.use_as_Int()
            Check(And(self._num_inputs.as_Int() >= 0,
                      self._num_inputs.as_Int() <= cur_env().max_num_inputs))

        return self._num_inputs

    @property
    def num_outputs(self) -> 'SymData':
        if self._num_outputs is None:
            self._num_outputs = SymData(name='tx_num_outputs')
            self._num_outputs.use_as_Int()
            Check(And(self._num_outputs.as_Int() >= 0,
                      self._num_outputs.as_Int() <= cur_env().max_num_outputs))

        return self._num_outputs

    @property
    def nVersion(self) -> 'SymData':
        if self._nVersion is None:
            self._nVersion = SymData(name='tx_nVersion',
                                     possible_sizes=(4,))
            self._nVersion.use_as_ByteSeq()
            Check(Or(*(self._nVersion.as_ByteSeq() == IntSeqVal(struct.pack('<i', v))
                       for v in POSSIBLE_TX_VERSIONS)))

        return self._nVersion

    @property
    def nLockTime(self) -> 'SymData':
        if self._nLockTime is None:
            self._nLockTime = SymData(name='tx_nLockTime', possible_sizes=(4,))
            self._nLockTime.use_as_ByteSeq()

        return self._nLockTime

    @property
    def weight(self) -> 'SymData':
        if self._weight is None:
            self._weight = SymData(name='tx_weight')
            self._weight.use_as_Int()
            Check(And(self._weight.as_Int() >= 0,
                      self._weight.as_Int() <= cur_env().max_tx_size*4))

        return self._weight

    @property
    def current_input_index(self) -> 'SymData':
        if self._current_input_index is None:
            self._current_input_index = SymData(name='current_input')
            self._current_input_index.use_as_Int()
            Check(
                And(self._current_input_index.as_Int() >= 0,
                    self._current_input_index.as_Int() < self.num_inputs.as_Int()))

        return self._current_input_index

    def values(self) -> list['SymData']:
        result: list['SymData'] = []
        for value in self.__dict__.values():
            if isinstance(value, TxValuesDict):
                result.extend(value.values())
            elif value:
                assert isinstance(value, SymData)
                result.append(value)

        return result

    def clone(self) -> 'TransactionFieldValues':
        inst = self.__class__()
        for name, value in self.__dict__.items():
            if isinstance(value, TxValuesDict):
                setattr(inst, name, value.clone_to(self))
            else:
                setattr(inst, name, value)

        return inst


class ExecState:
    def __init__(self,
                 stack: Optional[list['SymData']] = None,
                 altstack: Optional[list['SymData']] = None,
                 vfExec: Optional[list[bool]] = None):
        self.stack = stack or []
        self.altstack = altstack or []
        self.vfExec = vfExec or []

    def clone(self) -> 'ExecState':
        return self.__class__(
            stack=self.stack.copy(),
            altstack=self.altstack.copy(),
            vfExec=self.vfExec.copy())

    def __repr__(self) -> str:
        parts = []
        if self.stack:
            parts.append(
                "  stack:\n\t" + "\n\t".join(repr(elt)
                                             for elt in reversed(self.stack)))
        else:
            parts.append("  stack: <empty>")

        if self.altstack:
            parts.append("  altstack:\n\t"
                         + "\n\t".join(repr(elt)
                                       for elt in reversed(self.altstack)))

        if self.vfExec:
            parts.append(f'  vfExec: {self.vfExec}')

        return "\n\n".join(parts)


T_ExecContext = TypeVar('T_ExecContext', bound='ExecContext')


class ExecContext(SupportsFailureCodeCallbacks):
    pc = 0
    segwit_mode_op_count = 0
    failure: tuple[int, str] | None = None
    is_finalized: bool = False
    max_combined_stack_len = 0
    num_expunged_witnesses = 0
    tx: TransactionFieldValues
    _run_on_start: list[Callable[[], None]]
    _z3_on_start: list['z3.BoolRef']
    _set_of_single_value_data: set[str]
    _used_as_Int_maxsize: dict[str, tuple[int, int]]
    _enforcement_condition_positions: dict[str, set[int]]
    _data_refcounts: dict[str, int]
    _data_refcount_neighbors: dict[str, set['SymData']]
    unused_values: set['SymData']
    skip_enforcement_in_region: tuple[int, int] | None = None

    def __init__(
        self, *,
        branchpoint: 'Branchpoint',
        exec_state: Optional[ExecState] = None,
        exec_state_log: Optional[dict[int, ExecState]] = None,
        enforcements: Optional[list[Enforcement]] = None,
        constrained_values: Optional[dict[str, ConstrainedValue]] = None,
        model_values: Optional[dict[str, ConstrainedValue]] = None,
        known_bool_values: Optional[dict[str, bool]] = None,
        used_witnesses: Optional[list['SymData']] = None,
        sym_depth_register: Optional[list['SymDepth']] = None,
        warnings: Optional[list[tuple[int, str]]] = None,
        z3_warning_vars: Optional[list[tuple[int, 'SymData']]] = None,
        z3_used_types_for_vars: Optional[dict[str, set[SymDataRType]]] = None
    ):
        self.branchpoint = branchpoint
        self.exec_state = exec_state or ExecState()
        self.exec_state_log = exec_state_log or {}
        self.enforcements = enforcements or []
        self.constrained_values = constrained_values or {}
        self.model_values = model_values or {}
        self.known_bool_values = known_bool_values or {}
        self.used_witnesses = used_witnesses or []
        self.sym_depth_register = sym_depth_register or []
        self.warnings = warnings or []
        self.z3_warning_vars = z3_warning_vars or []
        self.z3_used_types_for_vars = z3_used_types_for_vars or {}
        self._run_on_start = []
        self._z3_on_start = []
        self._set_of_single_value_data = set()
        self._used_as_Int_maxsize = {}
        self._enforcement_condition_positions = {}
        self._data_refcounts = {}
        self._data_refcount_neighbors = {}
        self.unused_values = set()

    @property
    def stack(self) -> list['SymData']:
        return self.exec_state.stack

    @property
    def altstack(self) -> list['SymData']:
        return self.exec_state.altstack

    @property
    def vfExec(self) -> list[bool]:
        return self.exec_state.vfExec

    def add_warning(self, w: str) -> None:
        self.warnings.append((self.pc, w))

    def clone(self: T_ExecContext) -> T_ExecContext:
        assert not self.failure

        inst = self.__class__(
            branchpoint=self.branchpoint,
            exec_state=self.exec_state.clone(),
            exec_state_log=self.exec_state_log.copy(),
            constrained_values=deepcopy(self.constrained_values),
            model_values=deepcopy(self.model_values),
            known_bool_values=self.known_bool_values.copy(),
            used_witnesses=self.used_witnesses.copy(),
            sym_depth_register=self.sym_depth_register.copy(),
            warnings=self.warnings.copy(),
            z3_warning_vars=self.z3_warning_vars.copy(),
            z3_used_types_for_vars=deepcopy(self.z3_used_types_for_vars))

        with CurrentExecContext(inst):
            inst.tx = self.tx.clone()

        inst.pc = self.pc
        inst.segwit_mode_op_count = self.segwit_mode_op_count
        inst.failure = self.failure
        inst.is_finalized = self.is_finalized
        inst.max_combined_stack_len = self.max_combined_stack_len
        inst.num_expunged_witnesses = self.num_expunged_witnesses
        inst._set_of_single_value_data = self._set_of_single_value_data.copy()
        inst._used_as_Int_maxsize = self._used_as_Int_maxsize.copy()
        inst._enforcement_condition_positions = \
            deepcopy(self._enforcement_condition_positions)
        inst._data_refcounts = self._data_refcounts.copy()
        inst._data_refcount_neighbors = deepcopy(self._data_refcount_neighbors)
        inst.unused_values = self.unused_values.copy()

        for e in self.enforcements:
            inst.enforcements.append(e.clone(context=inst))

        return inst

    def branch(self: T_ExecContext, *,
               cond: Optional[Union['SymData', tuple['SymData', ...]]] = None,
               cond_designations: tuple[str, str] = ('True', 'False')
               ) -> T_ExecContext:

        assert cond_designations[0] != cond_designations[1]

        new_context = self.clone()
        new_context.exec_state_log[new_context.pc] = self.exec_state.clone()
        new_context.pc += 1

        bp = self.branchpoint  # save, because Branchpoint() will overwrite
        self.branchpoint.set_branches(
            (Branchpoint(pc=self.pc, cond=cond,
                         designation=cond_designations[0],
                         parent=bp, context=self, branch_index=0),
             Branchpoint(pc=self.pc, cond=cond,
                         designation=cond_designations[1],
                         parent=bp, context=new_context, branch_index=1)))

        z3_push_context()

        return new_context

    def run_on_start(self, fun: Callable[[], None]) -> None:
        self._run_on_start.append(fun)

    def on_start(self) -> None:
        if self.pc == 0:
            assert (not self._run_on_start) and (not self._z3_on_start), \
                "on-start routines are possible only for branches"
            return

        # run on-start routines as if we're still at the opcode
        # that created the branch
        self.pc -= 1

        try:
            with CurrentOp(g_script_body[self.pc]):
                for fun in self._run_on_start:
                    fun()
                for c, c_name in self._z3_on_start:
                    z3add(c, c_name)
                if self._z3_on_start or self._run_on_start:
                    # check only if assertions could be added
                    z3check()
        except ScriptFailure as sf:
            self.register_failure(self.pc, str(sf))
        finally:
            self._run_on_start.clear()
            self._z3_on_start.clear()
            # restore pc back to the curent position
            self.pc += 1

    def get_timeline_strings(self, *, skip_failed_branches: bool = True
                             ) -> list[str]:
        return self.branchpoint.get_timeline_strings(
            skip_failed_branches=skip_failed_branches)

    def register_failure(self, pc: int, err: str) -> None:
        assert err, "failure reason must not be empty"
        env = cur_env()
        if env.log_solving_attempts:
            err_to_report = err
            if err.startswith(SCRIPT_FAILURE_PREFIX_SOLVER):
                err_to_report = ', '.join(
                    set(fc[0] for fc in parse_failcodes(err)))

            env.solving_log(f'Failure: {err_to_report}')
            env.solving_log_ensure_empty_line()

        self.exec_state_log[pc] = self.exec_state.clone()
        self.failure = (pc, err)

    @property
    def failure_info(self) -> tuple[int, list[str]] | str:
        if not self.failure:
            return ''

        def info_at_pc(err: str, pc: int) -> str:
            if pc in self.exec_state_log:
                state_repr = f'\n\n{self.exec_state_log[pc]}'
            else:
                state_repr = ''

            return (f'{op_pos_repr(pc)} @ {op_pos_info(pc)}: '
                    f'{err}{state_repr}')

        pc, err = self.failure

        if not err.startswith(SCRIPT_FAILURE_PREFIX_SOLVER):
            return info_at_pc(err, pc)

        info_list = parse_failcodes(err)

        return pc, [info_at_pc(*info) for info in info_list]

    def stacktop(self, index: int) -> 'SymData':
        assert index < 0

        max_witnesses = MAX_STACK_SIZE-self.num_expunged_witnesses

        for _ in range((-index) - len(self.stack)):
            wit_no = len(self.used_witnesses)

            if len(self.stack)+1 > MAX_STACK_SIZE:
                raise ScriptFailure('stack overflow')
            if wit_no+1 > max_witnesses:
                raise ScriptFailure(
                    f"witness wit{wit_no} cannot be accessed, because having "
                    f"this many witnesses would cause stack overflow earlier")

            wit = SymData(name=f'wit{wit_no}', witness_number=wit_no)
            wit.increase_refcount()
            self.stack.insert(0, wit)
            self.used_witnesses.append(wit)

        v = self.stack[index]
        return v

    def push(self, v: 'SymData') -> None:
        if v.possible_sizes:
            # Note that when there's multiple sizes, they won't be above
            # MAX_SCRIPT_ELEMENT_SIZE, because of check in set_possible_sizes()
            if any(size > MAX_SCRIPT_ELEMENT_SIZE for size in v.possible_sizes):
                raise ScriptFailure(
                    f'attempt to push value of length {v.possible_sizes} but '
                    f'the limit is {MAX_SCRIPT_ELEMENT_SIZE} bytes')
        else:
            Check(v.Length() <= MAX_SCRIPT_ELEMENT_SIZE,
                  err_data_too_long())

        v.increase_refcount()
        self.stack.append(v)

    def popstack(self) -> 'SymData':
        assert len(self.stack) > 0, "stack underflow must be detected earlier"
        v = self.stack.pop()
        v.decrease_refcount()
        return v

    def add_enforcement(self, cond: 'SymData', *, name: str = '',
                        is_script_bool: bool = False) -> None:
        cond.increase_refcount()
        if self.skip_enforcement_in_region:
            start, end = self.skip_enforcement_in_region
            self.skip_enforcement_in_region = None
            if start <= self.pc <= end:
                return

        self.enforcements.append(
            Enforcement(cond, pc=self.pc, context=self, name=name,
                        is_script_bool=is_script_bool))

    def get_name_suffix(self) -> str:
        return f'@{op_pos_info(self.pc, separator="")}'


class IntLE64(bytes):

    MAX_VALUE = 0x7fffffffffffffff
    MIN_VALUE = -0x8000000000000000

    def __init__(self, v: bytes) -> None:
        if len(v) != 8:
            raise ScriptFailure('expected 8 bytes')

    @classmethod
    def from_int(cls, v: int) -> 'IntLE64':
        return cls(struct.pack(b"<q", v))

    def as_int(self) -> int:
        return int(struct.unpack(b"<q", self)[0])

    def __repr__(self) -> str:
        return f'le64({self.as_int()})'


class SymData:
    _args: tuple['SymData', ...] = ()
    _data_reference: str | None = None
    _data_reference_was_reset: bool = False
    _data_reference_aliases: set[str]
    _unique_name: str

    _Int: Optional['z3.ArithRef'] = None
    _Int64: Optional['z3.ArithRef'] = None
    _ByteSeq: Optional['z3.SeqSortRef'] = None
    _Length: Optional['z3.ArithRef'] = None

    def __init__(self, *, name: str | None = None,
                 args: Iterable['SymData'] = (),
                 witness_number: int | None = None,
                 static_value: str | bytes | bytearray | int | IntLE64 | None = None,
                 unique_name: str | None = None,
                 possible_sizes: Iterable[int] = (),
                 ) -> None:

        self._args = tuple(args)

        if name:
            if name.startswith('_'):
                raise ValueError("names starting with '_' are reserved")

            if name.count('_%_') and len(self._args) != 1:
                raise ValueError(
                    "the '_%_' marker is only applicable for one-argument "
                    "opcode names")

        self._name = name
        self._wit_no = witness_number
        self._data_reference_aliases = set()

        ctx = cur_context()
        pc = ctx.pc

        self._src_pc = pc

        if unique_name is None:
            bpc = ctx.branchpoint.pc
            branch_index = ctx.branchpoint.branch_index

            global g_stack_symdata_index
            assert g_stack_symdata_index is not None

            sd_idx = g_stack_symdata_index
            line_no_str = f'L{g_line_no_table[pc]}'
            branch_line_no_str = f'L{g_line_no_table[bpc]}'
            self._unique_name = \
                (f'{self._name or "_"}_{pc}{line_no_str}_{bpc}'
                 f'{branch_line_no_str}_{branch_index}_{sd_idx}')
            g_stack_symdata_index += 1
        else:
            self._unique_name = unique_name

        if witness_number:
            Check(self.Length() <= MAX_SCRIPT_ELEMENT_SIZE)

        if static_value is not None:
            self.set_static(static_value)

        if possible_sizes:
            self.set_possible_sizes(*(possible_sizes))

        self._failcodes: dict[str, 'FailureCodeDispatcher'] = {}

    def get_failcode_dispatcher(self, prefix: str) -> 'FailureCodeDispatcher':
        fc = self._failcodes.get(prefix)
        if fc is None:
            fc = FailureCodeDispatcher(f'{prefix}_{self.unique_name}')
            self._failcodes[prefix] = fc

        return fc

    @property
    def src_pc(self) -> int:
        return self._src_pc

    @property
    def name(self) -> str | None:
        return self._name

    @property
    def is_witness(self) -> bool:
        return self._wit_no is not None

    @property
    def args(self) -> tuple['SymData', ...]:
        return self._args

    @property
    def is_only_one_value_possible(self) -> bool:
        return self._unique_name in cur_context()._set_of_single_value_data

    def mark_as_only_one_value_possible(self) -> None:
        cur_context()._set_of_single_value_data.add(self._unique_name)

    @property
    def unique_name(self) -> str:
        return self._unique_name

    @property
    def refcount(self) -> int:
        return cur_context()._data_refcounts.get(self._unique_name, 0)

    def increase_refcount(self) -> None:
        cur_context()._data_refcounts[self._unique_name] = self.refcount + 1
        for arg in self.args:
            arg.increase_refcount()

    def decrease_refcount(self) -> None:
        refcount = self.refcount
        assert refcount >= 1
        cur_context()._data_refcounts[self._unique_name] = refcount - 1
        for arg in self.args:
            arg.decrease_refcount()

    def get_refcount_neighbors(self, include_self: bool = True
                               ) -> set['SymData']:
        rset = cur_context()._data_refcount_neighbors.get(self._unique_name,
                                                          set())
        if include_self:
            rset.add(self)
        return rset

    def add_refcount_neighbor(self, neighbor: 'SymData') -> None:
        if neighbor is self:
            return

        ctx = cur_context()
        if self._unique_name not in ctx._data_refcount_neighbors:
            ctx._data_refcount_neighbors[self._unique_name] = set()

        ctx._data_refcount_neighbors[self._unique_name].add(neighbor)

    def mark_as_enforcement_condition(self, pc: int) -> None:
        ctx = cur_context()
        if self._unique_name not in ctx._enforcement_condition_positions:
            ctx._enforcement_condition_positions[self._unique_name] = set()

        ctx._enforcement_condition_positions[self._unique_name].add(pc)

    def get_enforcement_deps(self, pc: int) -> set[tuple['SymData', int]]:
        deps: set[tuple['SymData', int]] = set()

        ecset = cur_context()._enforcement_condition_positions.get(
            self._unique_name, set())

        for epc in (epc for epc in ecset if epc >= pc):
            deps.add((self, epc))

        for arg in self._args:
            deps.update(arg.get_enforcement_deps(pc))

        return deps

    def get_constrained_value(self) -> ConstrainedValue | None:
        return cur_context().constrained_values.get(self._unique_name)

    def set_static(self, v: Union[T_ConstrainedValueValue, bytearray]) -> None:
        ctx = cur_context()
        cv = ctx.constrained_values.get(self._unique_name) or ConstrainedValue()
        cv.set_possible_values(v)
        ctx.constrained_values[self._unique_name] = cv
        self.mark_as_only_one_value_possible()
        self.update_solver_for_constrained_value(cv)

    def set_possible_values(
        self, *_values: Union[T_ConstrainedValueValue, bytearray],
        value_name: str = '', update_solver: bool = True
    ) -> None:
        ctx = cur_context()
        cv = ctx.constrained_values.get(self._unique_name) or ConstrainedValue()
        cv.set_possible_values(*_values, value_name=value_name)
        ctx.constrained_values[self._unique_name] = cv
        if update_solver:
            self.update_solver_for_constrained_value(cv)

    def set_possible_sizes(self, *_sizes: int, value_name: str = '',
                           update_solver: bool = True) -> None:
        ctx = cur_context()
        cv = ctx.constrained_values.get(self._unique_name) or ConstrainedValue()
        cv.set_possible_sizes(*_sizes, value_name=value_name)
        ctx.constrained_values[self._unique_name] = cv
        if update_solver:
            self.update_solver_for_constrained_value(cv)

    def set_data_reference(self, data_reference: str) -> None:
        if self._data_reference is not None or self._data_reference_was_reset:
            if not self._data_reference_was_reset:
                ctx = cur_context()
                ctx.warnings.append(
                    (ctx.pc,
                     f'Tried to replace data_reference {self._data_reference} with data_reference '
                     f'{data_reference} at {op_pos_info(ctx.pc)}, data_reference is reset to '
                     f'empty, to prevent confusion'))
                self._data_reference_was_reset = True

            self._data_reference = None
        else:
            self._data_reference = data_reference

    @property
    def is_static(self) -> bool:
        if cv := self.get_constrained_value():
            return cv.single_value is not None

        return False

    @property
    def possible_sizes(self) -> tuple[int, ...]:
        if cv := self.get_constrained_value():
            return cv.possible_sizes

        return ()

    def as_bool(self) -> bool:
        if cv := self.get_constrained_value():
            return cv.as_bool()

        non_static_value_error('cannot be represented as bool')

    def as_scriptnum_int(self) -> int:
        if cv := self.get_constrained_value():
            max_size, _ = self._get_used_as_Int_maxsize()
            return cv.as_scriptnum_int(max_size=max_size)

        non_static_value_error('cannot be represented as int')

    def as_le64(self) -> int:
        if cv := self.get_constrained_value():
            return cv.as_le64()

        non_static_value_error('cannot be represented as le64')

    def as_bytes(self) -> bytes:
        if cv := self.get_constrained_value():
            return cv.as_bytes()

        non_static_value_error('cannot be represented as bytes')

    def _maybe_data_reference(self) -> str | None:
        if not g_do_process_data_reference_names:
            return None

        if self._unique_name in g_seen_named_values:
            return None

        data_reference = self._data_reference
        if data_reference is None:
            return None

        cr = self.canonical_repr()
        for dr in ([data_reference] + list(self._data_reference_aliases)):
            while True:
                for other_cr, other_entry in g_data_reference_names_table.items():
                    if other_cr != cr and dr in other_entry:
                        dr_altname = f"{dr}'"
                        if dr == data_reference:
                            data_reference = dr_altname

                        dr = dr_altname
                        break
                else:
                    break

            entry = g_data_reference_names_table.get(cr, {})
            entry[dr] = (self, cur_context())
            g_data_reference_names_table[cr] = entry

        return f'&{data_reference}'

    def set_model_value(self, cv: Optional[ConstrainedValue]) -> None:
        if cv is None:
            cv = self.get_constrained_value()

        if cv is not None:
            cur_context().model_values[self._unique_name] = cv

    def model_repr(self) -> str | None:
        mv = self.get_model_value()
        if mv is not None:
            return repr(mv)

        if cv := self.get_constrained_value():
            if cv.value_name:
                return cv.value_name

            return repr(cv)

        return None

    def get_model_value(self) -> ConstrainedValue | None:
        if cv := self.get_constrained_value():
            pvals = cv.possible_values
            if pvals:
                if len(pvals) == 1:
                    return cv

        if model_cv := cur_context().model_values.get(self._unique_name):
            return model_cv

        return None

    def canonical_repr(self) -> str:
        if self._name is None:
            if cv := self.get_constrained_value():
                if cv.single_value is not None:
                    return cv.canonical_repr()

        name = self._name or '_'

        if self._args:
            args = '(' + ', '.join(a.canonical_repr() for a in self._args) + ')'
        else:
            args = ''

        if cur_env().tag_data_with_position and not self.is_witness:
            return f'{name}{args}@{self.src_pc}'

        return f'{name}{args}'

    def __repr__(self) -> str:
        return self.readable_repr()

    def readable_repr(self, with_name: str = '') -> str:  # noqa
        if dr := self._maybe_data_reference():
            return dr

        name = with_name or self._name or '_'

        result_str: str | None = None
        if self._name == 'CAT':
            assert len(self._args) == 2
            result_str = f'{self._args[0]}.{self._args[1]}'
        else:
            if m := re.search('_%_', name):
                cv = self._args[0].get_constrained_value()
                if cv and isinstance(cv.single_value, int):
                    result_str = \
                        f'{name[:m.start()]}_{cv.single_value}_{name[m.end():]}'
                else:
                    name = f'{name[:m.start()]}_{name[m.end():]}'

            if result_str is None:
                if self._args:
                    args = '(' + ', '.join(repr(a) for a in self._args) + ')'
                else:
                    args = ''

                result_str = f'{name}{args}'

        if self._name is None:
            if cv := self.get_constrained_value():
                return repr(cv)

        if cur_env().tag_data_with_position and not self.is_witness:
            return f'{result_str}@{self.src_pc}'

        return result_str

    def _var_usageset(self) -> set[SymDataRType]:
        ctx = cur_context()
        if self._unique_name not in ctx.z3_used_types_for_vars:
            ctx.z3_used_types_for_vars[self._unique_name] = set()

        return ctx.z3_used_types_for_vars[self._unique_name]

    def _use_var_as(self, rtype: SymDataRType) -> None:
        self._var_usageset().add(rtype)

    def _was_used_as(self, rtype: SymDataRType) -> bool:
        return rtype in self._var_usageset()

    @property
    def was_used_as_Int(self) -> bool:
        return self._was_used_as(SymDataRType.INT)

    @property
    def was_used_as_ByteSeq(self) -> bool:
        return self._was_used_as(SymDataRType.BYTESEQ)

    @property
    def was_used_as_Int64(self) -> bool:
        return self._was_used_as(SymDataRType.INT64)

    @property
    def was_used_as_Length(self) -> bool:
        return self._was_used_as(SymDataRType.LENGTH)

    @property
    def _name_Int(self) -> str:
        return f'{self._unique_name}_Int'

    @property
    def _name_Int64(self) -> str:
        return f'{self._unique_name}_Int64'

    @property
    def _name_ByteSeq(self) -> str:
        return f'{self._unique_name}_ByteSeq'

    @property
    def _name_Length(self) -> str:
        return f'{self._unique_name}_Length'

    def set_as_Int(self, v: Union[int, 'z3.ArithRef'],
                   max_size: int = 4) -> None:
        if max_size > 5:
            raise ValueError(f'unsupported max_size {max_size}')

        if isinstance(v, int):
            Check(Or(v > -(2**((max_size)*8-1)),
                     v < (2**((max_size)*8-1))),
                  err_scriptnum_out_of_bounds())
            self.set_static(v)

        Check(self.use_as_Int(max_size=max_size) == v)

    def set_as_Int64(self, v: Union[int, 'z3.ArithRef']) -> None:
        if isinstance(v, int):
            if v < IntLE64.MIN_VALUE or v > IntLE64.MAX_VALUE:
                raise ScriptFailure('Value out of 64-bit range')

            self.set_static(IntLE64.from_int(v))

        Check(self.use_as_Int64() == v)

    # While we can have access to length via z3.Length(self._ByteSeq),
    # having separate integer variable for it speeds up the solving
    def use_as_Length(self, *, _byteseq: Optional['z3.SeqSortRef'] = None
                      ) -> Union[int, 'z3.ArithRef']:
        length = self.Length()
        if self.was_used_as_Length:
            return length

        if self._Length is not None:
            # if length was ever used as a symbol, we need to use that symbol
            length = self._Length

        if _byteseq is not None:
            # we are called from use_as_ByteSeq(), prevent recursion
            byteseq = _byteseq
        else:
            # we need to always call use_as_ByteSeq(),
            # as the use of Length implies use of ByteSeq
            byteseq = self.use_as_ByteSeq(_from_use_as_Length=True)
            # if ByteSeq was ever used as a symbol, we need to use
            # that symbol, even though use_as_ByteSeq() might return
            # z3.SeqSort(z3.IntSort()) produced from static bytes
            if self._ByteSeq is not None:
                byteseq = self._ByteSeq

        if self._Length is None and self._ByteSeq is None:
            # If both _Length and _ByteSeq was not set at this point,
            # this means that self was static before any of these two
            # symbols were accessed, and also means that these symbols
            # will always remain as None
            assert self.is_static
        elif cur_env().z3_enabled:
            Check(length == Length(byteseq))

        if self._Length is not None:
            if self.possible_sizes:
                Check(Or(*(length == size for size in self.possible_sizes)))
            else:
                Check(length <= MAX_SCRIPT_ELEMENT_SIZE, err_data_too_long())

        self._use_var_as(SymDataRType.LENGTH)

        # self.Length() because the value could be static,
        # even if the symbol was used at some point
        return self.Length()

    def use_as_ByteSeq(self, _from_use_as_Length: bool = False
                       ) -> Union[bytes, 'z3.SeqSortRef']:
        byteseq = self.as_ByteSeq()
        if self.was_used_as_ByteSeq:
            return byteseq

        if self._ByteSeq is not None:
            # if byteseq was ever used as a symbol, we need to use that symbol
            byteseq = self._ByteSeq

            if cv := self.get_constrained_value():
                if cv.possible_values:
                    Check(Or(*(byteseq == IntSeqVal(vb)
                               for vb in cv.values_as_bytes())))

        if not _from_use_as_Length:
            # we need to always use_as_Length(), as use of ByteSeq
            # imples that Check(length = Length(byteseq)) is done,
            # unless both are static
            self.use_as_Length(_byteseq=byteseq)

        if self.was_used_as_Int and self._Int is not None:
            assert self._Int64 is None
            assert not self.was_used_as_Int64
            scriptnum_to_sym_integer(byteseq, self._Int,
                                     max_size=max(self.possible_sizes))

        if self.was_used_as_Int64 and self._Int64 is not None:
            assert self._Int is None
            assert not self.was_used_as_Int
            le64_signed_to_integer(byteseq, self._Int64)

        self._use_var_as(SymDataRType.BYTESEQ)

        # self.as_ByteSeq() because the value could be static,
        # even if the symbol was used at some point
        return self.as_ByteSeq()

    def _get_used_as_Int_maxsize(self) -> tuple[int, int]:
        ctx = cur_context()
        return ctx._used_as_Int_maxsize.get(self._unique_name, (4, ctx.pc))

    def use_as_Int(self, max_size: int = 4) -> Union[int, 'z3.ArithRef']:
        ctx = cur_context()
        if self.was_used_as_Int:
            assert self.possible_sizes
            prev_max_size = max(self.possible_sizes)
            if prev_max_size > max_size:
                assert prev_max_size == 5
                Check(And(self.as_Int() >= MIN_SCRIPTNUM_INT,
                          self.as_Int() <= MAX_SCRIPTNUM_INT),
                      err_scriptnum_out_of_bounds())

            return self.as_Int()

        ctx._used_as_Int_maxsize[self._unique_name] = (max_size, ctx.pc)

        # must call as_Int() first, so the symbol can be set
        value = self.as_Int()

        possible_sizes = tuple(range(max_size+1))

        value_name = 'ScriptNum(...)'
        if cv := self.get_constrained_value():
            value_name = cv.value_name or value_name
            if cv.possible_values and self._Int is not None:
                Check(Or(*(self._Int == vi
                           for vi in cv.values_as_scriptnum_int(
                               max_size=max_size))))

        self.set_possible_sizes(*possible_sizes, value_name=value_name,
                                update_solver=False)

        if self.was_used_as_Length and self._Length is not None:
            Check(Or(*(self._Length == size for size in possible_sizes)))

        if self.was_used_as_ByteSeq and self._Int is not None:
            assert self.was_used_as_Length
            scriptnum_to_sym_integer(self.as_ByteSeq(), self._Int,
                                     max_size=max_size)

        self._use_var_as(SymDataRType.INT)

        return value

    def use_as_Int64(self) -> Union[int, 'z3.ArithRef']:
        # must call as_Int64() first, so the symbol can be set
        value = self.as_Int64()
        if self.was_used_as_Int64:
            return value

        value_name = 'LE64(...)'
        got_possible_values = False
        if cv := self.get_constrained_value():
            value_name = cv.value_name or value_name
            if cv.possible_values:
                got_possible_values = True
                if self._Int64 is not None:
                    Check(Or(*(self._Int64 == v64 for v64 in cv.values_as_le64())))

        self.set_possible_sizes(8, value_name=value_name, update_solver=False)

        if not got_possible_values and self._Int64 is not None:
            # LE64 is a 64-bit 'machine int', and thus it can represent -(2**63)
            Check(And(self._Int64 <= 2**63-1, self._Int64 >= -2**63),
                  err_int64_out_of_bounds())

        if self.was_used_as_Length and self._Length is not None:
            Check(self._Length == 8, err_le64_wrong_size())

        if self.was_used_as_ByteSeq and self._Int64 is not None:
            le64_signed_to_integer(self.as_ByteSeq(), self._Int64)

        self._use_var_as(SymDataRType.INT64)

        return value

    def Length(self) -> Union[int, 'z3.ArithRef']:
        if len(self.possible_sizes) == 1:
            return self.possible_sizes[0]

        assert not self.is_static

        if self._Length is None:
            self._Length = Int(self._name_Length)

        return self._Length

    def as_ByteSeq(self) -> Union[bytes, 'z3.SeqSortRef']:
        if self.is_static:
            if cur_env().z3_enabled:
                return IntSeqVal(self.as_bytes())

            return self.as_bytes()

        if not cur_env().z3_enabled and self.known_bool_value is not None and \
                self.possible_sizes in ((1,), (0,)):
            if self.known_bool_value:
                assert self.possible_sizes == (1,)
                return b'\x01'
            else:
                assert self.possible_sizes == (0,)
                return b''

        if self._ByteSeq is None:
            self._ByteSeq = Const(self._name_ByteSeq, IntSeqSortRef())

        return self._ByteSeq

    def as_Int(self) -> Union[int, 'z3.ArithRef']:
        if self.was_used_as_Int64:
            raise ScriptFailure('LE64 cannot be converted to scriptnum')

        if self.is_static:
            return self.as_scriptnum_int()

        if not cur_env().z3_enabled and self.known_bool_value is not None:
            return int(self.known_bool_value)

        if self._Int is None:
            self._Int = Int(self._name_Int)

        return self._Int

    def as_Int64(self) -> Union[int, 'z3.ArithRef']:
        if self.was_used_as_Int:
            raise ScriptFailure('scriptnum cannot be converted to LE64')

        if self.is_static:
            return self.as_le64()

        if self._Int64 is None:
            self._Int64 = Int(self._name_Int64)

        return self._Int64

    def update_solver_for_constrained_value(self, cv: ConstrainedValue) -> None:
        if not cv.possible_values:
            assert cv.possible_sizes
            if self.was_used_as_Length and self._Length is not None:
                Check(Or(*(self._Length == size for size in cv.possible_sizes)))

            return

        if self.was_used_as_Length and self._Length is not None:
            Check(Or(*(self._Length == len(vb) for vb in cv.values_as_bytes())))

        if self.was_used_as_Int and self._Int is not None:
            max_size, _ = self._get_used_as_Int_maxsize()
            Check(Or(*(self._Int == vi
                       for vi in cv.values_as_scriptnum_int(max_size=max_size))))

        if self.was_used_as_Int64 and self._Int64 is not None:
            Check(Or(*(self._Int64 == vi64 for vi64 in cv.values_as_le64())))

        if self.was_used_as_ByteSeq and self._ByteSeq is not None:
            Check(Or(*(self._ByteSeq == IntSeqVal(vb)
                       for vb in cv.values_as_bytes())))

    def update_model_values_request_dict(
        self,
        mvdict_req: dict[str, tuple[str, SymDataRType]],
        namemap: dict[str, 'SymData']
    ) -> None:
        if self.was_used_as_Int:
            name = self._name_Int
        elif self.was_used_as_Int64:
            name = self._name_Int64
        elif self.was_used_as_ByteSeq:
            name = self._name_ByteSeq
        elif self.was_used_as_Length:
            name = self._name_Length
        else:
            return

        if not self.is_static:
            if self.was_used_as_Int:
                assert self._Int is not None
                dname = self._Int.decl().name()
                rtype = SymDataRType.INT
            elif self.was_used_as_Int64:
                assert self._Int64 is not None
                dname = self._Int64.decl().name()
                rtype = SymDataRType.INT64
            elif self.was_used_as_ByteSeq:
                assert self._ByteSeq is not None
                dname = self._ByteSeq.decl().name()
                rtype = SymDataRType.BYTESEQ
            elif self.was_used_as_Length:
                assert self._Length is not None
                dname = self._Length.decl().name()
                rtype = SymDataRType.LENGTH
            else:
                raise AssertionError("unreachable")

            assert name not in mvdict_req
            mvdict_req[name] = (dname, rtype)

        assert name not in namemap
        namemap[name] = self

    def check_only_one_value_possible(self, *, name: str = '') -> None:
        if cv := cur_context().model_values.get(self._unique_name):
            if cv.single_value is None:
                return

            if self.was_used_as_Int:
                max_size, _ = self._get_used_as_Int_maxsize()
                check_exp = self.as_Int() != cv.as_scriptnum_int(max_size=max_size)
            elif self.was_used_as_Int64:
                check_exp = self.as_Int64() != cv.as_le64()
            elif self.was_used_as_ByteSeq:
                check_exp = self.as_ByteSeq() != IntSeqVal(cv.as_bytes())
            else:
                return

            if not is_cond_possible(check_exp, self, name=name,
                                    fail_msg='  - only one possible value'):
                self.mark_as_only_one_value_possible()

    @property
    def known_bool_value(self) -> bool | None:
        return cur_context().known_bool_values.get(self._unique_name)

    def set_known_bool(self, value: bool, set_size: bool = False) -> None:
        if set_size:
            self.set_possible_sizes(int(value))

        cur_context().known_bool_values[self._unique_name] = value


class SymDepth(SymData):

    def __init__(self, *,
                 depth_at_exec: int,
                 num_known_witnesses: int,
                 **kwargs: Any) -> None:
        super().__init__(**kwargs)
        self._depth_at_exec = depth_at_exec
        self._num_known_witnesses = num_known_witnesses
        self.pc_of_last_static_update: int | None = None

    @property
    def depth(self) -> int:
        return (self._depth_at_exec + len(cur_context().used_witnesses)
                - self._num_known_witnesses)

    def set_static(self, v: int | str | bytes | bytearray | IntLE64) -> None:
        self.pc_of_last_static_update = cur_context().pc
        super().set_static(v)

    def set_possible_sizes(self, *_sizes: int, value_name: str = '',
                           update_solver: bool = True) -> None:
        self.pc_of_last_static_update = cur_context().pc
        super().set_possible_sizes(*_sizes, value_name=value_name,
                                   update_solver=update_solver)

    def set_possible_values(
        self, *_values: Union[T_ConstrainedValueValue, bytearray],
        value_name: str = '', update_solver: bool = True
    ) -> None:
        self.pc_of_last_static_update = cur_context().pc
        super().set_possible_values(*_values, value_name=value_name,
                                    update_solver=update_solver)

    def canonical_repr(self) -> str:
        return self._unique_name

    def __repr__(self) -> str:
        if dr := self._maybe_data_reference():
            return dr

        if cur_context().is_finalized:
            result_str = f'{self._name}:{self.depth}'
        else:
            result_str = f'{self._name}:>={self.depth}'

        if cur_env().tag_data_with_position:
            return f'{result_str}@{self.src_pc}'

        return result_str


def maybe_sort_args(*_args: SymData) -> Iterable[SymData]:
    if not cur_env().use_deterministic_arguments_order:
        return _args

    args = list(_args)
    args.sort(key=lambda a: a.canonical_repr())

    return args


def should_skip_immediately_failed_branch() -> bool:
    env = cur_env()
    if not env.skip_immediately_failed_branches_on:
        return False

    ctx = cur_context()
    start = ctx.pc + 1
    end = start + len(env.skip_immediately_failed_branches_on)
    if end <= len(g_script_body) and \
            g_script_body[start:end] == env.skip_immediately_failed_branches_on:
        ctx.skip_enforcement_in_region = (start, end)
        return True

    return False


def symex_op(ctx: ExecContext, op_or_sd: OpCode | ScriptData) -> bool:
    try:
        with CurrentOp(op_or_sd):
            was_executed = _symex_op(ctx, op_or_sd)
    except ScriptFailure as sf:
        ctx.register_failure(ctx.pc, str(sf))
        was_executed = False

    return was_executed


@dataclass
class PluginHelperFunctions:
    stacktop: Callable[[int], 'SymData']
    stacktop64: Callable[[int], 'SymData']
    push: Callable[['SymData'], None]
    popstack: Callable[[], None]
    erase: Callable[[int], None]


def _symex_op(ctx: ExecContext, op_or_sd: OpCode | ScriptData) -> bool:  # noqa

    tx = ctx.tx

    env = cur_env()

    popped_or_erased_values: list[SymData] = []

    def stacktop(index: int) -> 'SymData':
        return ctx.stacktop(index)

    def stacktop64(index: int) -> 'SymData':
        v = ctx.stacktop(index)
        if v.is_static:
            if len(v.as_bytes()) != 8:
                raise ScriptFailure(
                    f'expected 8 bytes for first arg, got {len(v.as_bytes())}')
            v.set_static(IntLE64.from_int(v.as_le64()))

        v.use_as_Int64()

        return v

    def push(v: SymData) -> None:
        ctx.push(v)

    def popstack() -> None:
        v = ctx.popstack()
        popped_or_erased_values.append(v)

    def erase(index: int) -> None:
        # we have access the stack element before deleting it to check
        # for stack bounds. Also we need to remember it to check refcount later
        v = stacktop(index)
        popped_or_erased_values.append(v)
        del ctx.stack[index]

    def symresult(op: OpCode, *args: SymData) -> SymData:
        return SymData(name=op.name, args=args)

    def sym_successflag(op: OpCode, *args: SymData) -> SymData:
        name_pseudo_arg = SymData(name=op.name)
        sf = SymData(name='SUCCESS_FLAG', args=(name_pseudo_arg, *args),
                     possible_sizes=(1, 0))
        sf.use_as_Int()
        # help solver by adding explicit assertions about this value
        Check(Or(sf.as_Int() == 1, sf.as_Int() == 0))
        Check(Implies(sf.Length() == 1, sf.as_ByteSeq()[0] == 1))
        return sf

    def refcount_neighbors(*neighbors: SymData, args: Iterable['SymData'] = ()
                           ) -> None:
        assert len(neighbors) > 1
        unused_args = set(args)
        for nb1 in neighbors:
            for arg in unused_args.copy():
                if arg in nb1.args:
                    unused_args.remove(arg)

            for nb2 in neighbors:
                nb1.add_refcount_neighbor(nb2)
                nb2.add_refcount_neighbor(nb1)

        for arg in unused_args:
            # If the arg is not present in any of the neighbors, that means
            # these neighbors are probably taken from already-set tx values.
            # Increase refcount to prevent this arg reported as unused
            arg.increase_refcount()

    def check_scriptdata_len() -> None:
        if isinstance(op_or_sd, ScriptData):
            sd = op_or_sd
            assert isinstance(sd, ScriptData)
            if isinstance(sd.value, str):
                vlen = len(sd.value.encode('utf-8'))
            elif isinstance(sd.value, bytes):
                vlen = len(sd.value)
            elif isinstance(sd.value, int):
                vlen = len(integer_to_scriptnum(sd.value))
            else:
                assert sd.value is None
                vlen = None

            if vlen is not None:
                Check(vlen <= MAX_SCRIPT_ELEMENT_SIZE, err_data_too_long())

    fExec = all(ctx.vfExec)

    r: SymData

    check_scriptdata_len()

    if isinstance(op_or_sd, OpCode):
        op = op_or_sd
        if fExec or (OP_IF <= op and op <= OP_ENDIF):
            pass
        else:
            return False
    elif not fExec:
        return False

    if isinstance(op_or_sd, ScriptData):
        def scope() -> None:
            sd = op_or_sd
            assert isinstance(sd, ScriptData)

            if env.minimaldata_flag_strict and sd.is_non_minimal:
                raise ScriptFailure(
                    'non-minimal immediate data encountered when '
                    'minimaldata flag handling is strict')

            if sd.name and sd.name.startswith('$'):
                if sd.name not in g_data_placeholders:
                    g_data_placeholders[sd.name] = SymData(
                        name=sd.name, unique_name=f'_dph_{sd.name}')

                data = g_data_placeholders[sd.name]
            else:
                data = SymData(name=sd.name, static_value=sd.value)

            push(data)

        scope()
    elif op == OP_NOP:
        pass
    elif op == OP_0:

        push(SymData(name=op.name, static_value=b''))

    elif op == OP_1NEGATE or ((op >= OP_1) and (op <= OP_16)):

        push(SymData(name=op.name, static_value=(int(op) - (int(OP_1) - 1))))

    elif op == OP_CHECKLOCKTIMEVERIFY:
        def scope() -> None:
            bn1 = stacktop(-1)

            locktime = bn1.use_as_Int(max_size=5)

            Check(locktime >= 0, err_negative_argument())

            nLockTime = FreshInt('nLockTime')

            le32_unsigned_to_integer(tx.nLockTime.as_ByteSeq(), nLockTime)

            no_locktime_type_mismatch = Or(And(nLockTime < LOCKTIME_THRESHOLD,
                                               locktime < LOCKTIME_THRESHOLD),
                                           And(nLockTime >= LOCKTIME_THRESHOLD,
                                               locktime >= LOCKTIME_THRESHOLD))

            Check(no_locktime_type_mismatch, err_locktime_type_mismatch())

            # Implication is added here because othersise "timelock_in_effect"
            # error might not be shown by z3, and "locktime_type_mismatch"
            # is shown where actually no mismatch
            Check(Implies(no_locktime_type_mismatch, locktime <= nLockTime),
                  err_locktime_timelock_in_effect())

            Check(tx.nSequence.as_ref(tx.current_input_index.as_Int())
                  != IntSeqVal(SEQUENCE_FINAL_bytes),
                  err_cltv_nsequence_final())

            z3check()

            ctx.add_enforcement(SymData(name='CLTV', args=(bn1,)))

        scope()
    elif op == OP_CHECKSEQUENCEVERIFY:
        def scope() -> None:
            bn1 = stacktop(-1)
            csv = SymData(name='CSV', args=(bn1,))

            tx_nVersion = FreshInt('tx_nVersion')
            le32_unsigned_to_integer(tx.nVersion.as_ByteSeq(), tx_nVersion)
            Check(Or(tx_nVersion >= 2), err_bad_tx_version())

            nsequence = bn1.use_as_Int(max_size=5)

            csv_disabled = \
                BitMask(nsequence, SEQUENCE_LOCKTIME_DISABLE_FLAG) != 0

            Check(nsequence >= 0, err_negative_argument())

            txToSequence = FreshInt('txToSequence')

            le32_unsigned_to_integer(
                tx.nSequence.as_ref(tx.current_input_index.as_Int()),
                txToSequence)

            nLockTimeMask = SEQUENCE_LOCKTIME_TYPE_FLAG | SEQUENCE_LOCKTIME_MASK
            txToSequenceMasked = BitMask(txToSequence, nLockTimeMask)
            nSequenceMasked = BitMask(nsequence, nLockTimeMask)

            Check(Or(csv_disabled,
                     And(txToSequenceMasked < SEQUENCE_LOCKTIME_TYPE_FLAG,
                         nSequenceMasked < SEQUENCE_LOCKTIME_TYPE_FLAG),
                     And(txToSequenceMasked >= SEQUENCE_LOCKTIME_TYPE_FLAG,
                         nSequenceMasked >= SEQUENCE_LOCKTIME_TYPE_FLAG)),
                  err_nsequence_type_mismatch())

            Check(Or(csv_disabled, nSequenceMasked <= txToSequenceMasked),
                  err_nsequence_timelock_in_effect())

            z3check()

            if isinstance(csv_disabled, bool) and csv_disabled:
                bn1.increase_refcount()  # mark as used
            else:
                ctx.add_enforcement(csv)

        scope()
    elif op in (OP_IF, OP_NOTIF):
        def scope() -> None:
            fValue = False

            if fExec:

                cond = stacktop(-1)
                cond.increase_refcount()

                # do this before branch() so any z3 constraints that is
                # added will be present in the previous constraint frame
                if env.minimalif_flag:
                    cond_int = cond.use_as_Int()

                    if not isinstance(cond_int, int) and \
                            not env.z3_enabled and \
                            cond.known_bool_value is not None:
                        # here the value could actually be non-minimal-encoded
                        # zero. This will result in script failure because
                        # MINIMALIF is in effect. But the report will not
                        # show this as a failed path, because without
                        # z3_enabled, we cannot track this
                        cond_int = int(cond.known_bool_value)
                else:
                    cond_int = use_as_script_bool(cond)

                if isinstance(cond, int):
                    fValue = bool(cond_int)
                else:
                    fValue = True

                if op == OP_IF:
                    new_context = ctx.branch(cond=cond)
                else:
                    fValue = not fValue
                    new_context = ctx.branch(
                        cond=cond,
                        cond_designations=('False', 'True'))

                new_context.vfExec.append(False)

                def fail_on_invalid_cond() -> None:
                    expected_cond_int = int(not fValue)

                    Check(cond_int == expected_cond_int,
                          err_branch_condition_invalid(),
                          enforcement_condition=cond)

                    if not env.z3_enabled:
                        cond.set_known_bool(bool(expected_cond_int))

                    z3check()

                    new_context.popstack()

                new_context.run_on_start(fail_on_invalid_cond)

                expected_cond_int = int(fValue)

                if env.minimalif_flag:
                    Check(Or(cond_int == 0, cond_int == 1), err_minimalif())

                Check(cond_int == expected_cond_int,
                      err_branch_condition_invalid(),
                      enforcement_condition=cond)

                if not env.z3_enabled:
                    cond.set_known_bool(bool(expected_cond_int))

                z3check()

                popstack()

            ctx.vfExec.append(True)

        scope()
    elif op == OP_ELSE:

        if len(ctx.vfExec) == 0:
            raise ScriptFailure('unbalanced conditional (on OP_ELSE)')

        ctx.vfExec[-1] = not ctx.vfExec[-1]

    elif op == OP_ENDIF:

        if len(ctx.vfExec) == 0:
            raise ScriptFailure('unbalanced conditional (on OP_ENDIF)')

        ctx.vfExec.pop()

    elif op == OP_VERIFY:
        def scope() -> None:
            val = stacktop(-1)

            Check(use_as_script_bool(val) != 0, err_verify(),
                  enforcement_condition=val)

            z3check()

            ctx.add_enforcement(val, is_script_bool=True)

            popstack()

        scope()
    elif op == OP_RETURN:

        raise ScriptFailure('OP_RETURN encountered')

    elif op == OP_TOALTSTACK:

        ctx.altstack.append(stacktop(-1))
        ctx.altstack[-1].increase_refcount()
        popstack()

    elif op == OP_FROMALTSTACK:

        if len(ctx.altstack) < 1:
            raise ScriptFailure('altstack underflow')

        ctx.altstack[-1].decrease_refcount()
        push(ctx.altstack[-1])

        ctx.altstack.pop()
        assert len(ctx.altstack) >= 0

    elif op == OP_2DROP:

        _ = stacktop(-1)
        _ = stacktop(-2)

        popstack()
        popstack()

    elif op == OP_2DUP:
        def scope() -> None:
            vch1 = stacktop(-2)
            vch2 = stacktop(-1)

            push(vch1)
            push(vch2)

        scope()
    elif op == OP_3DUP:
        def scope() -> None:
            vch1 = stacktop(-3)
            vch2 = stacktop(-2)
            vch3 = stacktop(-1)

            push(vch1)
            push(vch2)
            push(vch3)

        scope()
    elif op == OP_2OVER:
        def scope() -> None:
            vch1 = stacktop(-4)
            vch2 = stacktop(-3)

            push(vch1)
            push(vch2)

        scope()
    elif op == OP_2ROT:
        def scope() -> None:
            vch1 = stacktop(-6)
            vch2 = stacktop(-5)

            erase(-6)
            erase(-5)

            push(vch1)
            push(vch2)
        scope()
    elif op == OP_2SWAP:
        def scope() -> None:
            vch1 = stacktop(-4)
            vch2 = stacktop(-3)

            ctx.stack[-4] = stacktop(-2)
            ctx.stack[-2] = vch1

            ctx.stack[-3] = stacktop(-1)
            ctx.stack[-1] = vch2

        scope()
    elif op == OP_IFDUP:
        def scope() -> None:

            cond = stacktop(-1)

            new_context = ctx.branch(cond=cond)

            new_context.run_on_start(
                lambda: Check(use_as_script_bool(cond) == 0,
                              err_branch_condition_invalid(),
                              enforcement_condition=cond))
            new_context.run_on_start(lambda: cond.set_known_bool(False))

            Check(use_as_script_bool(cond) != 0,
                  err_branch_condition_invalid(),
                  enforcement_condition=cond)
            cond.set_known_bool(True)

            z3check()

            push(cond)

        scope()
    elif op == OP_DEPTH:
        def scope() -> None:
            r = SymDepth(name=op.name,
                         depth_at_exec=len(ctx.stack),
                         num_known_witnesses=len(ctx.used_witnesses))

            ctx.sym_depth_register.append(r)

            r_int = r.use_as_Int(
                max_size=len(integer_to_scriptnum(MAX_STACK_SIZE)))

            Check(r_int >= r.depth)
            Check(r_int < MAX_STACK_SIZE - len(ctx.altstack))

            z3check()

            push(r)

        scope()
    elif op == OP_DROP:

        _ = stacktop(-1)
        popstack()

    elif op == OP_DUP:

        push(stacktop(-1))

    elif op == OP_NIP:

        erase(-2)

    elif op == OP_OVER:

        push(stacktop(-2))

    elif op in (OP_PICK, OP_ROLL):
        def scope() -> None:
            bn1 = stacktop(-1)
            bn1.increase_refcount()  # mark as used

            # NOTE: It is possible to create execution branches for
            # different values of the argument.
            # We should be able allow this for small values of the argument without
            # blowing up simulation time. The question is if PICK/ROLL with
            # dynamic arguments happen in useful scripts at all.
            if not bn1.is_static:
                raise non_static_value_error(f'{op.name}: non-static argument')

            val_pos = bn1.as_scriptnum_int()
            if val_pos < 0:
                raise ScriptFailure(f'{op.name}: negative argument')
            if val_pos >= MAX_STACK_SIZE:
                raise ScriptFailure(f'{op.name}: argument too big')
            popstack()
            val = stacktop(-val_pos-1)
            if op == OP_ROLL:
                erase(-val_pos-1)
            push(val)

        scope()
    elif op == OP_ROT:
        def scope() -> None:
            vch1 = stacktop(-3)
            vch2 = stacktop(-2)
            vch3 = stacktop(-1)
            ctx.stack[-3] = vch2
            ctx.stack[-2] = vch3
            ctx.stack[-1] = vch1

        scope()
    elif op == OP_SWAP:
        def scope() -> None:
            vch1 = stacktop(-2)
            vch2 = stacktop(-1)
            ctx.stack[-2] = vch2
            ctx.stack[-1] = vch1

        scope()
    elif op == OP_TUCK:
        def scope() -> None:
            vch1 = stacktop(-2)
            vch2 = stacktop(-1)
            popstack()
            popstack()
            push(vch2)
            push(vch1)
            push(vch2)

        scope()
    elif op == OP_CAT:
        def scope() -> None:
            vch1 = stacktop(-2)
            vch2 = stacktop(-1)

            r = symresult(op, vch1, vch2)

            if vch1.is_static and vch2.is_static:
                r.set_static(vch1.as_bytes() + vch2.as_bytes())
            else:
                Check(r.use_as_ByteSeq() == Concat(vch1.use_as_ByteSeq(),
                                                   vch2.use_as_ByteSeq()))

            Check(r.Length() <= MAX_SCRIPT_ELEMENT_SIZE,
                  err_data_too_long())

            z3check()

            popstack()
            popstack()
            push(r)

        scope()
    elif op == OP_SIZE:
        def scope() -> None:
            val = stacktop(-1)
            r = symresult(op, val)

            r.set_as_Int(val.use_as_Length())

            z3check()

            push(r)

        scope()
    elif op in (OP_LEFT, OP_RIGHT):
        def scope() -> None:
            vch1 = stacktop(-2)
            bn2 = stacktop(-1)

            r = symresult(op, vch1, bn2)

            start = bn2.use_as_Int()
            Check(start >= 0, err_negative_argument())

            if isinstance(start, int):
                if vch1.is_static:
                    vch1_bytes = vch1.as_bytes()

                    if op == OP_RIGHT:
                        if start >= len(vch1_bytes):
                            r_data = b''
                        else:
                            r_data = vch1_bytes[start:]
                    elif op == OP_LEFT:
                        if start >= len(vch1_bytes):
                            r_data = vch1_bytes
                        else:
                            r_data = vch1_bytes[:start]
                    else:
                        assert op in (OP_LEFT, OP_RIGHT)

                    r.set_static(r_data)

            if not r.is_static:
                data = vch1.use_as_ByteSeq()
                r_data = r.use_as_ByteSeq()
                if op == OP_RIGHT:
                    Check(If(start >= vch1.Length(),
                             r.Length() == 0,
                             r_data == Extract(
                                 data, start, vch1.Length() - start)))
                elif op == OP_LEFT:
                    Check(If(start >= vch1.Length(),
                             r_data == data,
                             r_data == Extract(data, 0, start)))
                else:
                    assert op in (OP_LEFT, OP_RIGHT)

            z3check()

            popstack()
            popstack()
            push(r)

        scope()
    elif op in (OP_SUBSTR, OP_SUBSTR_LAZY):
        def scope() -> None:
            vch1 = stacktop(-3)
            bn2 = stacktop(-2)
            bn3 = stacktop(-1)

            r = symresult(op, vch1, bn2, bn3)
            start = bn2.use_as_Int()
            length = bn3.use_as_Int()
            vch1.use_as_ByteSeq()

            datalen = vch1.Length()

            if op == OP_SUBSTR:
                Check(And(start >= 0, length >= 0),
                      err_negative_argument())
                Check(start + length <= datalen,
                      err_argument_above_bounds())
            else:
                start = If(start < 0, 0, start)
                length = If(length < 0, 0, If(start + length > datalen,
                                              datalen - start,
                                              length))

            if bn2.is_static and bn3.is_static and vch1.is_static:
                r.set_static(vch1.as_bytes()[start:start+length])
            else:
                r_byteseq = r.use_as_ByteSeq()
                if op == OP_SUBSTR:
                    Check(r_byteseq == Extract(vch1.as_ByteSeq(), start, length))
                else:
                    Check(If(start >= datalen,
                             r.Length() == 0,
                             r_byteseq == Extract(vch1.as_ByteSeq(), start, length)))

            z3check()

            popstack()
            popstack()
            popstack()
            push(r)

        scope()
    elif op == OP_RSHIFT:
        def scope() -> None:
            vch1 = stacktop(-2)
            bn = stacktop(-1)

            r = symresult(op, vch1, bn)
            full_bits = bn.use_as_Int()

            Check(full_bits >= 0, err_negative_argument())

            full_bytes: Union[int, 'z3.ArithRef']
            if isinstance(full_bits, int):
                full_bytes = full_bits // 8
            else:
                full_bytes = full_bits / 8
                assert isinstance(full_bytes, (z3.ArithRef, DummyExpr))

            if isinstance(full_bits, int):
                if vch1.is_static:
                    data = vch1.as_bytes()

                    bits = full_bits % 8

                    if full_bytes >= len(data):
                        r.set_static(b'')
                    else:
                        r_bdata = bytearray(data[full_bytes:])

                        temp = 0
                        for i in range(len(r_bdata)-1, -1, -1):
                            temp = (r_bdata[i] << (8 - bits)) | ((temp << 8) & 0xff00)
                            r_bdata[i] = (temp & 0xff00) >> 8

                        # 0x0fff >> 4 == 0x00ff or 0xff, reduce to minimal representation
                        for i in range(len(r_bdata)-1, -1, -1):
                            if r_bdata[i] != 0:
                                break

                            r_bdata = r_bdata[:i]

                        r.set_static(r_bdata)

            if not r.is_static:
                data = vch1.use_as_ByteSeq()
                r_data = r.use_as_ByteSeq()
                tmp_dstseq = FreshConst(IntSeqSortRef(), 'tmp_dstseq')
                bits = (8 - full_bits % 8) % 8
                add_op_lshift_constraints(src=data, dst=tmp_dstseq,
                                          shift_bits=bits, shift_bytes=0)
                drop_bytes = full_bytes + If(bits == 0, 0, 1)
                Check(r_data == Extract(tmp_dstseq, drop_bytes,
                                        Length(tmp_dstseq)-drop_bytes))

            z3check()

            popstack()
            popstack()
            push(r)

        scope()
    elif op == OP_LSHIFT:
        def scope() -> None:
            vch1 = stacktop(-2)
            bn = stacktop(-1)

            r = symresult(op, vch1, bn)

            full_bits = bn.use_as_Int()

            full_bytes: Union[int, 'z3.ArithRef']
            if isinstance(full_bits, int):
                full_bytes = full_bits // 8
            else:
                full_bytes = full_bits / 8
                assert isinstance(full_bytes, (z3.ArithRef, DummyExpr))

            bits = full_bits % 8

            Check(full_bits >= 0, err_negative_argument())
            Check(vch1.Length() + full_bytes + If(bits != 0, 1, 0)
                  <= MAX_SCRIPT_ELEMENT_SIZE,
                  err_data_too_long())

            if isinstance(full_bits, int):
                if vch1.is_static:
                    data = vch1.as_bytes()

                    r_data = bytearray((b'\x00'*full_bytes) + data + b'')

                    temp = 0
                    for i in range(len(r_data)):
                        temp = (r_data[i] << bits) | (temp >> 8)
                        r_data[i] = temp & 0xff

                    # reduce to minimal representation
                    for i in range(len(r_data)-1, -1, -1):
                        if r_data[i] != 0:
                            break

                        r_data = r_data[:i]

                    r.set_static(r_data)

            if not r.is_static:
                add_op_lshift_constraints(
                    src=vch1.use_as_ByteSeq(), dst=r.use_as_ByteSeq(),
                    shift_bits=full_bits % 8,
                    shift_bytes=full_bytes)

            z3check()

            popstack()
            popstack()
            push(r)

        scope()
    elif op == OP_INVERT:
        def scope() -> None:
            vch1 = stacktop(-1)

            r = symresult(op, vch1)

            if vch1.is_static:
                r_data_static = bytearray(vch1.as_bytes())
                for i in range(len(r_data_static)):
                    r_data_static[i] = ~r_data_static[i] & 0xFF

                r.set_static(r_data_static)
            elif env.z3_enabled:
                idx = FreshInt('idx')
                data = vch1.use_as_ByteSeq()
                r_data = r.use_as_ByteSeq()

                Check(r.Length() == vch1.Length())
                Check(
                    z3.ForAll(idx,
                              Implies(
                                  And(idx >= 0, idx < vch1.Length()),
                                  And(data[idx] >= 0,
                                      data[idx] < 0x100,
                                      r_data[idx] == 0xFF - data[idx]))))

            z3check()

            popstack()
            push(r)

        scope()
    elif op in (OP_AND, OP_OR, OP_XOR):
        def scope() -> None:
            vch1 = stacktop(-1)
            vch2 = stacktop(-2)

            r = symresult(op, *maybe_sort_args(vch1, vch2))

            Check(vch1.Length() == vch2.Length(), err_length_mismatch())

            if vch1.is_static and vch2.is_static:
                r_bdata = bytearray(vch1.as_bytes())
                vch2_data = vch2.as_bytes()

                for i in range(len(r_bdata)):
                    if op == OP_AND:
                        r_bdata[i] &= vch2_data[i]
                    elif op == OP_OR:
                        r_bdata[i] |= vch2_data[i]
                    elif op == OP_XOR:
                        r_bdata[i] ^= vch2_data[i]

                r.set_static(r_bdata)
            elif vch1.is_static:
                vch2.set_possible_sizes(len(vch1.as_bytes()))
            elif vch2.is_static:
                vch1.set_possible_sizes(len(vch2.as_bytes()))

            if not r.is_static and env.z3_enabled:
                sym_bitfun = env.get_sym_bitfun8(op)
                idx = FreshInt('idx')
                data_a = vch1.use_as_ByteSeq()
                data_b = vch2.use_as_ByteSeq()
                r_data = r.use_as_ByteSeq()
                Check(
                    z3.ForAll(
                        idx,
                        Implies(And(idx >= 0, idx < vch1.Length()),
                                And(data_a[idx] >= 0,
                                    data_a[idx] < 0x100,
                                    data_b[idx] >= 0,
                                    data_b[idx] < 0x100,
                                    r_data[idx]
                                    == sym_bitfun(data_a[idx], data_b[idx])))))

            z3check()

            popstack()
            popstack()
            push(r)

        scope()
    elif op in (OP_EQUAL, OP_EQUALVERIFY):
        def scope() -> None:
            vch1 = stacktop(-2)
            vch2 = stacktop(-1)

            r = symresult(op, *maybe_sort_args(vch1, vch2))

            # access as_ByteSeq before checking canonical repr,
            # so that constraints on BytesSeq symbolic variables will be
            # always set
            bytes1 = vch1.use_as_ByteSeq()
            bytes2 = vch2.use_as_ByteSeq()

            r.set_possible_values(0, 1)

            if vch1.canonical_repr() == vch2.canonical_repr():
                if vch1.is_static and vch2.is_static:
                    assert vch1.as_bytes() == vch2.as_bytes()

                # equal canonical repr means equal byte values
                Check(bytes1 == bytes2)

                r.set_as_Int(1)
            elif (env.minimaldata_flag and
                  vch1.was_used_as_Int and vch2.was_used_as_Int):
                # equal(add($a, 1), sub(add($a ,2), 1) might not be
                # detected as 'always true' if $a is not restricted in any way
                # this seems to be limitation of the solver, where it cannot
                # infer equality after some arithmetic operationn and then
                # converting the results to bytes via scriptnum_to_sym_integer
                # therefore we check if data was used as integers before, and
                # if so, we will compare data as integers, but only if
                # minimaldata flag is set.
                r.set_as_Int(If(vch1.as_Int() == vch2.as_Int(), 1, 0))
                # bytes equality must match integer equality, but do this check
                # just in case
                Check(If(r.as_Int() == 1, bytes1 == bytes2, bytes1 != bytes2))
            else:
                r.set_as_Int(If(bytes1 == bytes2, 1, 0))

            if op == OP_EQUALVERIFY:
                Check(r.as_Int() != 0, err_equalverify(),
                      enforcement_condition=r)
                maybe_enforce_equality_when_z3_disabled(vch1, vch2)

            z3check()

            popstack()
            popstack()

            if op == OP_EQUALVERIFY:
                ctx.add_enforcement(r, name='EQUAL')
            else:
                push(r)

        scope()
    elif op in (OP_1ADD, OP_1SUB, OP_NEGATE, OP_ABS, OP_NOT, OP_0NOTEQUAL):
        def scope() -> None:
            bn = stacktop(-1)

            r = symresult(op, bn)

            op_table: dict[OpCode, Callable[[Union[int, 'z3.ArithRef']],
                                            Union[int, 'z3.ArithRef']]] = \
                {
                    OP_1ADD:      lambda v: v + 1,
                    OP_1SUB:      lambda v: v - 1,
                    OP_NEGATE:    lambda v: (-v),
                    OP_ABS:       lambda v: Abs(v),
                    OP_NOT:       lambda v: If(v == 0, 1, 0),
                    OP_0NOTEQUAL: lambda v: If(v != 0, 1, 0)
                }

            if op not in op_table:
                raise AssertionError(f"Unhandled binary opcode OP_{op.name}")

            if op in (OP_NOT, OP_0NOTEQUAL):
                r.set_possible_values(0, 1)

            max_size = 4
            if op in (OP_1ADD, OP_1SUB):
                max_size = 5

            r.set_as_Int(op_table[op](bn.use_as_Int()), max_size=max_size)

            z3check()

            popstack()
            push(r)

        scope()
    elif op in (OP_ADD, OP_SUB, OP_BOOLAND, OP_BOOLOR, OP_NUMEQUAL,
                OP_NUMEQUALVERIFY, OP_NUMNOTEQUAL, OP_LESSTHAN,
                OP_GREATERTHAN, OP_LESSTHANOREQUAL, OP_GREATERTHANOREQUAL,
                OP_MIN, OP_MAX):
        def scope() -> None:
            bn2 = stacktop(-1)
            bn1 = stacktop(-2)

            if op in (OP_ADD, OP_BOOLAND, OP_BOOLOR,
                      OP_NUMEQUAL, OP_NUMEQUALVERIFY, OP_NUMNOTEQUAL):

                r = symresult(op, *maybe_sort_args(bn1, bn2))
            else:
                r = symresult(op, bn1, bn2)

            # access as_Int before checking canonical repr,
            # so that constrants on Int symbolic variables will be
            # always set
            arg1 = bn1.use_as_Int()
            arg2 = bn2.use_as_Int()

            op_table: dict[OpCode, Callable[[Union[int, 'z3.ArithRef'],
                                             Union[int, 'z3.ArithRef']],
                                            Union[int, 'z3.ArithRef']]] = \
                {
                    OP_ADD:                lambda a, b: a + b,
                    OP_SUB:                lambda a, b: a - b,
                    OP_BOOLAND:            lambda a, b: If(And(a != 0, b != 0), 1, 0),
                    OP_BOOLOR:             lambda a, b: If(Or(a != 0, b != 0), 1, 0),
                    OP_NUMEQUAL:           lambda a, b: If(a == b, 1, 0),
                    OP_NUMEQUALVERIFY:     lambda a, b: If(a == b, 1, 0),
                    OP_NUMNOTEQUAL:        lambda a, b: If(a != b, 1, 0),
                    OP_LESSTHAN:           lambda a, b: If(a < b, 1, 0),
                    OP_GREATERTHAN:        lambda a, b: If(a > b, 1, 0),
                    OP_LESSTHANOREQUAL:    lambda a, b: If(a <= b, 1, 0),
                    OP_GREATERTHANOREQUAL: lambda a, b: If(a >= b, 1, 0),
                    OP_MIN:                lambda a, b: If(a < b, a, b),
                    OP_MAX:                lambda a, b: If(a > b, a, b)
                }

            if op not in op_table:
                raise AssertionError(f"Unhandled binary opcode OP_{op.name}")

            if op in (OP_BOOLAND, OP_BOOLOR, OP_NUMEQUAL, OP_NUMEQUALVERIFY,
                      OP_NUMNOTEQUAL, OP_LESSTHAN, OP_GREATERTHAN,
                      OP_LESSTHANOREQUAL, OP_GREATERTHANOREQUAL):
                r.set_possible_values(0, 1)

            if not isinstance(arg1, int) and not isinstance(arg2, int):
                cr1 = bn1.canonical_repr()
                cr2 = bn2.canonical_repr()

                if cr1 == cr2:
                    # if canonical representations match,
                    # values must also match
                    Check(arg1 == arg2)

                    if op == OP_SUB:
                        r.set_static(0)
                    elif op in (OP_NUMEQUAL, OP_NUMEQUALVERIFY):
                        r.set_static(1)
                    elif op == OP_NUMNOTEQUAL:
                        r.set_static(0)

            max_size = 4
            if op in (OP_ADD, OP_SUB):
                max_size = 5

            r.set_as_Int(op_table[op](arg1, arg2), max_size=max_size)

            if op == OP_NUMEQUALVERIFY:
                Check(r.as_Int() != 0, err_numequalverify(),
                      enforcement_condition=r)
                maybe_enforce_equality_when_z3_disabled(bn1, bn2,
                                                        is_numeric=True)

            z3check()

            popstack()
            popstack()

            if op == OP_NUMEQUALVERIFY:
                ctx.add_enforcement(r, name='NUMEQUAL')
            else:
                ctx.push(r)

        scope()
    elif op == OP_WITHIN:
        def scope() -> None:
            bn1 = stacktop(-3)
            bn2 = stacktop(-2)
            bn3 = stacktop(-1)

            r = symresult(op, bn1, bn2, bn3)

            arg1 = bn1.use_as_Int()
            arg2 = bn2.use_as_Int()
            arg3 = bn3.use_as_Int()

            r.set_possible_values(0, 1)
            r.set_as_Int(If(And(arg2 <= arg1, arg1 < arg3), 1, 0))

            z3check()

            popstack()
            popstack()
            popstack()
            push(r)

        scope()
    elif op in (OP_RIPEMD160, OP_SHA1, OP_SHA256, OP_HASH160, OP_HASH256):
        def scope() -> None:
            vch = stacktop(-1)

            r = symresult(op, vch)

            hf_table: dict[str, Callable[[bytes], bytes]] = {
                'RIPEMD160': lambda v: ripemd160(v),
                'SHA1': lambda v: hashlib.sha1(v).digest(),
                'SHA256': lambda v: hashlib.sha256(v).digest(),
                'HASH160': lambda v: ripemd160(hashlib.sha256(v).digest()),
                'HASH256': lambda v: hashlib.sha256(
                    hashlib.sha256(v).digest()).digest()
            }

            if vch.is_static:
                r.set_static(hf_table[op.name](vch.as_bytes()))
            else:
                r.set_possible_sizes(len(hf_table[op.name](b'')))

            if env.z3_enabled:
                sym_fun, collision_possible = env.get_sym_hashfun(op)
                data = vch.use_as_ByteSeq()
                r_data = r.use_as_ByteSeq()
                Check(sym_fun(data) == r_data)
                seq = FreshConst(IntSeqSortRef(), 'seq')
                if collision_possible:
                    Check(z3.ForAll(
                        seq, Implies(seq == data, sym_fun(seq) == sym_fun(data))))
                else:
                    Check(z3.ForAll(
                        seq, (sym_fun(seq) == sym_fun(data)) == (seq == data)))

            z3check()

            popstack()
            push(r)

        scope()
    elif op == OP_CODESEPARATOR:

        # CODESEPARATOR only affects signature checking, which we do not
        # simulate, so we treat CODESEPARATOR as NOP
        pass

    elif op in (OP_CHECKSIG, OP_CHECKSIGVERIFY):
        def scope() -> None:
            vchSig = stacktop(-2)
            vchPubKey = stacktop(-1)

            # TODO: examine SIGHASH flags
            r = symresult(op, vchSig, vchPubKey)

            vchPubKey.use_as_ByteSeq()
            r.use_as_Int()
            r.set_possible_values(0, 1)

            if vchSig.is_static:
                if vchSig.as_bytes() == b'':
                    if op == OP_CHECKSIGVERIFY:
                        raise ScriptFailure(f'{op.name} with empty signature')
                    else:
                        r.set_static(0)
            else:
                vchSig.use_as_ByteSeq()

            if env.sigversion == SigVersion.TAPSCRIPT:
                maybe_upgradeable_pub = add_xonly_pubkey_constraints(vchPubKey)
                htype = add_schnorr_sig_constraints(vchSig, maybe_upgradeable_pub)
            else:
                htype, is_valid_R_S = add_ecdsa_sig_constraints(vchSig)
                checksig_could_succeed = And(is_valid_R_S,
                                             add_pubkey_constraints(vchPubKey))
                Check(Implies(Not(checksig_could_succeed), r.as_Int() == 0))

            add_checksig_arg_constraints(vchSig, vchPubKey, htype, r.as_Int())

            if env.nullfail_flag:
                Check((vchSig.Length() == 0) == (r.as_Int() == 0),
                      err_signature_nullfail())
            else:
                Check(Implies(vchSig.Length() == 0, r.as_Int() == 0))

            if op == OP_CHECKSIGVERIFY:
                Check(r.as_Int() != 0, err_checksigverify(),
                      enforcement_condition=r)

            z3check()

            popstack()
            popstack()

            if op == OP_CHECKSIGVERIFY:
                ctx.add_enforcement(r, name='CHECKSIG')
            else:
                push(r)

        scope()
    elif op == OP_CHECKSIGADD:
        def scope() -> None:
            vchSig = stacktop(-3)
            bn = stacktop(-2)
            vchPubKey = stacktop(-1)

            r = symresult(op, vchSig, bn, vchPubKey)

            vchSig.use_as_ByteSeq()
            bn.use_as_Int()
            vchPubKey.use_as_ByteSeq()
            r.use_as_Int()

            checksig_result = FreshInt('checksig_result')

            maybe_upgradeable_pub = add_xonly_pubkey_constraints(vchPubKey)
            htype = add_schnorr_sig_constraints(vchSig, maybe_upgradeable_pub)
            add_checksig_arg_constraints(vchSig, vchPubKey, htype,
                                         checksig_result)

            Check(checksig_result == If(vchSig.Length() == 0, 0, 1))
            Check(r.as_Int() == bn.as_Int() + checksig_result)

            popstack()
            popstack()
            popstack()
            push(r)

        scope()
    elif op in (OP_CHECKMULTISIG, OP_CHECKMULTISIGVERIFY):
        def scope() -> None:
            stackpos = 1
            nKeysCount = stacktop(-stackpos)

            if not nKeysCount.is_static:
                non_static_value_error(
                    f"cannot use it for number of keys for "
                    f"{op.name} at {op_pos_info(ctx.pc)}")

            if nKeysCount.as_scriptnum_int() < 0 or \
                    nKeysCount.as_scriptnum_int() > MAX_PUBKEYS_PER_MULTISIG:
                raise ScriptFailure(
                    f'{op.name}: invalid keys count {nKeysCount.as_scriptnum_int()}')

            ctx.segwit_mode_op_count += nKeysCount.as_scriptnum_int()
            if ctx.segwit_mode_op_count > MAX_OPS_PER_SCRIPT_SEGWIT_MODE:
                raise ScriptFailure('Maximum opcode count is reached')

            pubkeys = []
            for _ in range(nKeysCount.as_scriptnum_int()):
                stackpos += 1
                pub = stacktop(-stackpos)
                pub.use_as_ByteSeq()
                pubkeys.append(pub)

            stackpos += 1

            nSigsCount = stacktop(-stackpos)
            if not nSigsCount.is_static:
                non_static_value_error(
                    f"cannot use it for number of signatures for {op.name} "
                    f"at {op_pos_info(ctx.pc)}")

            if nSigsCount.as_scriptnum_int() < 0 or \
                    nSigsCount.as_scriptnum_int() > nKeysCount.as_scriptnum_int():
                raise ScriptFailure(
                    f'{op.name}: invalid signature count {nKeysCount.as_scriptnum_int()}')

            signatures = []
            for _ in range(nSigsCount.as_scriptnum_int()):
                stackpos += 1
                sig = stacktop(-stackpos)
                sig.use_as_ByteSeq()
                signatures.append(sig)

            r = symresult(op, nKeysCount, *pubkeys, nSigsCount, *signatures)

            if len(signatures) == 0:
                r.set_static(1)
            else:
                r.use_as_Int()
                r.set_possible_values(0, 1)

                isig = 0
                ikey = 0
                sigcnt = nSigsCount.as_scriptnum_int()
                keyscnt = nKeysCount.as_scriptnum_int()
                while sigcnt > 0:
                    sig = signatures[isig]
                    pub = pubkeys[ikey]

                    _, is_valid_R_S = add_ecdsa_sig_constraints(sig)
                    checksig_could_succeed = And(is_valid_R_S,
                                                 add_pubkey_constraints(pub),
                                                 (sig.Length() != 0))

                    if not isinstance(checksig_could_succeed, bool) or \
                            checksig_could_succeed:
                        isig += 1
                        sigcnt -= 1

                    ikey += 1
                    keyscnt -= 1

                    if sigcnt > keyscnt:
                        r.set_static(0)
                        break

                if env.nullfail_flag:
                    Check(Implies(r.as_Int() == 0,
                                  And(*[s.Length() == 0 for s in signatures])),
                          err_signature_nullfail())

                if op == OP_CHECKMULTISIGVERIFY:
                    Check(r.as_Int() != 0, err_checkmultisigverify(),
                          enforcement_condition=r)

            # A bug causes CHECKMULTISIG to consume one extra argument
            # whose contents were not checked in any way.
            #
            # Unfortunately this is a potential source of mutability,
            # so optionally verify it is exactly equal to zero prior
            # to removing it from the stack.
            bugbyte = stacktop(-1-len(pubkeys)-len(signatures)-2)
            if env.nulldummy_flag:
                bugbyte_enfc = SymData(name='NULLDUMMY', args=(bugbyte,))
                if bugbyte.is_static:
                    if len(bugbyte.as_bytes()) > 0:
                        raise ScriptFailure(f'{op.name}: extra byte is not zero')
                    bugbyte_enfc.set_static(1)
                else:
                    Check(bugbyte.use_as_Length() == 0,
                          err_checkmultisig_bugbyte_zero(),
                          enforcement_condition=bugbyte_enfc)

            z3check()

            popstack()
            for _ in pubkeys:
                popstack()
            popstack()
            for _ in signatures:
                popstack()

            # pop bugbyte
            popstack()

            if bugbyte.is_static or not env.nulldummy_flag:
                # Prevent mis-detection as unused value
                bugbyte.increase_refcount()
            else:
                ctx.add_enforcement(bugbyte_enfc)

            if op == OP_CHECKMULTISIGVERIFY:
                ctx.add_enforcement(r, name='CHECKMULTISIG')
            else:
                push(r)

        scope()
    elif op == OP_DETERMINISTICRANDOM:
        def scope() -> None:
            vchSeed = stacktop(-3)
            bnMin = stacktop(-2)
            bnMax = stacktop(-1)

            r = symresult(op, vchSeed, bnMin, bnMax)

            Check(bnMin.use_as_Int() <= bnMax.use_as_Int(),
                  err_argument_above_bounds())

            if bnMin.is_static and bnMax.is_static:
                if bnMin.as_scriptnum_int() == bnMax.as_scriptnum_int():
                    r.set_static(bnMin.as_scriptnum_int())

            if not r.is_static:
                r.use_as_Int()
                Check(And(r.as_Int() >= bnMin.as_Int(),
                          r.as_Int() < bnMin.as_Int() + bnMax.as_Int()))

            z3check()

            popstack()
            popstack()
            popstack()
            push(r)

        scope()
    elif op in (OP_CHECKSIGFROMSTACK, OP_CHECKSIGFROMSTACKVERIFY):
        def scope() -> None:
            vchSig = stacktop(-3)
            vchData = stacktop(-2)
            vchPubKey = stacktop(-1)

            # TODO: extract SIGHASH flags from vchSig if it is static
            r = symresult(op, vchSig, vchData, vchPubKey)

            vchSig.use_as_ByteSeq()
            vchData.use_as_ByteSeq()
            vchPubKey.use_as_ByteSeq()
            r.use_as_Int()
            r.set_possible_values(0, 1)

            if env.sigversion == SigVersion.TAPSCRIPT:
                maybe_upgradeable_pub = add_xonly_pubkey_constraints(vchPubKey)
                Check(Or(maybe_upgradeable_pub,
                         vchSig.Length() == 0,
                         vchSig.Length() == 64),
                      err_invalid_signature_length())
            else:
                # Sigs from stack have no hash byte, need to add dummy byte
                if vchSig.is_static:
                    sig = vchSig.as_bytes() + b'\x01'
                else:
                    sig = Concat(vchSig.as_ByteSeq(), IntSeqVal(b'\x01'))

                _, is_valid_R_S = add_ecdsa_sig_constraints(sig, num_extra_bytes=1)

                checksig_could_succeed = And(is_valid_R_S,
                                             add_pubkey_constraints(vchPubKey))
                Check(Implies(Not(checksig_could_succeed), r.as_Int() == 0))

            add_checksigfromstack_arg_constraints(
                vchSig, vchData, vchPubKey, r.as_Int())

            Check(Implies(vchSig.Length() == 0, r.as_Int() == 0))

            # pre-tapscript, CHECKSIGFROMSTACK has VERIFY semantics

            if op == OP_CHECKSIGFROMSTACKVERIFY or \
                    env.sigversion != SigVersion.TAPSCRIPT:

                Check(r.as_Int() != 0, err_checksigfromstackverify(),
                      enforcement_condition=r)

            z3check()

            popstack()
            popstack()
            popstack()

            if op == OP_CHECKSIGFROMSTACKVERIFY or \
                    env.sigversion != SigVersion.TAPSCRIPT:
                ctx.add_enforcement(r, name='CHECKSIGFROMSTACK')

            if op != OP_CHECKSIGFROMSTACKVERIFY:
                push(r)

        scope()
    elif op == OP_SHA256INITIALIZE:
        def scope() -> None:
            vch = stacktop(-1)
            r = symresult(op, vch)
            if vch.is_static:
                csha256 = CSHA256()
                CSHA256_SafeWrite(csha256, vch)
                CSHA256_Save(csha256, r)
            else:
                data = vch.use_as_ByteSeq()
                datalen = vch.Length()
                r_data = r.use_as_ByteSeq()

                if isinstance(datalen, int):
                    num_chunks = datalen // 8
                else:
                    num_chunks = datalen / 8

                bits_save = FreshInt('bits_save_init')
                bytes_tail = datalen % 64
                Check(bits_save == datalen * 8)
                le64_unsigned_to_integer(Extract(r_data, 32, 8), bits_save)
                Check(r.Length() == 40 + bytes_tail)
                Check(Extract(r_data, 40, bytes_tail)
                      == Extract(data, num_chunks * 64, bytes_tail))

                # if data length is less than 64, the midstate will be initial
                Check(Implies(datalen < 64,
                              Extract(r_data, 0, 32)
                              == IntSeqVal(CSHA256().Midstate())))

            z3check()

            popstack()
            push(r)

        scope()
    elif op == OP_SHA256UPDATE:
        def scope() -> None:
            sha256ctx = stacktop(-2)
            vch = stacktop(-1)

            sha256ctx.use_as_ByteSeq()
            vch.use_as_ByteSeq()
            r = symresult(op, sha256ctx, vch)

            bits_load = FreshInt('bits_load_update')
            bits_save = FreshInt('bits_save_update')

            if sha256ctx.is_static:
                csha256 = CSHA256_Load(op, sha256ctx)
                z3add(bits_load == csha256.bytes_count * 8)
                if vch.is_static:
                    CSHA256_SafeWrite(csha256, vch)
                    CSHA256_Save(csha256, r)
            else:
                sym_CSHA256_Load(sha256ctx, bits_load)

            Check(bits_save == bits_load + vch.Length() * 8)

            if not r.is_static:
                data = vch.as_ByteSeq()
                r_data = r.use_as_ByteSeq()

                le64_unsigned_to_integer(Extract(r_data, 32, 8), bits_save)
                datalen = (bits_save / 8)
                Check(datalen <= SHA256_MAX, err_invalid_sha256_context())
                Check(r.Length() == 40 + datalen % 64)
                Check(Extract(r_data, 40, datalen % 64)
                      == If(
                          (bits_load / 8) % 64 + vch.Length() >= 64,
                          Extract(data,
                                  vch.Length() - datalen % 64,
                                  datalen % 64),
                          Concat(Extract(sha256ctx.as_ByteSeq(),
                                         40,
                                         sha256ctx.Length() - 40),
                                 data)))

                # if data length is less than 64, the midstate will be initial
                Check(Implies(datalen < 64,
                              Extract(r_data, 0, 32)
                              == IntSeqVal(CSHA256().Midstate())))

            z3check()

            popstack()
            popstack()
            push(r)

        scope()
    elif op == OP_SHA256FINALIZE:
        def scope() -> None:
            sha256ctx = stacktop(-2)
            vch = stacktop(-1)

            sha256ctx.use_as_ByteSeq()
            vch.use_as_ByteSeq()
            r = symresult(op, sha256ctx, vch)

            if sha256ctx.is_static:
                csha256 = CSHA256_Load(op, sha256ctx)
                if vch.is_static:
                    csha256.Write(vch.as_bytes())
                    r.set_static(csha256.Finalize())
            else:
                # check validity of sha256ctx
                bits_load = FreshInt('bits_load_finalize')
                sym_CSHA256_Load(sha256ctx, bits_load)

            if not r.is_static:
                r.set_possible_sizes(32)

            z3check()

            popstack()
            popstack()
            push(r)

        scope()
    elif op in (OP_INSPECTINPUTOUTPOINT, OP_INSPECTINPUTASSET,
                OP_INSPECTINPUTVALUE, OP_INSPECTINPUTSCRIPTPUBKEY,
                OP_INSPECTINPUTSEQUENCE, OP_INSPECTINPUTISSUANCE):
        def scope() -> None:
            bn = stacktop(-1)

            index = bn.use_as_Int()

            Check(index >= 0, err_negative_argument())

            if isinstance(index, int) and index >= env.max_num_inputs:
                raise ScriptFailure(f'{op.name}: index too big')

            Check(bn.as_Int() < tx.num_inputs.as_Int(),
                  err_argument_above_bounds())

            if op == OP_INSPECTINPUTOUTPOINT:

                prevout_n = tx.input_prevout_n.get_known(index)
                if not prevout_n:
                    prevout_n = SymData(name='INPUT_%_OUTPOINT_PREVOUT_N',
                                        args=(bn,), possible_sizes=(4,))
                    prevout_n.use_as_ByteSeq()
                    tx.input_prevout_n[index] = prevout_n

                    temp_prevout_n = FreshInt('temp_prevout_n')
                    le32_unsigned_to_integer(prevout_n.as_ByteSeq(),
                                             temp_prevout_n)
                    Check(temp_prevout_n <= env.max_num_outputs)

                outpoint_flag = tx.input_outpoint_flag.get_known(index)
                if not outpoint_flag:
                    outpoint_flag = SymData(name='INPUT_%_OUTPOINT_FLAG',
                                            args=(bn,))
                    outpoint_flag.use_as_ByteSeq()
                    outpoint_flag.set_possible_values(
                        *(bytes([v]) for v in (0, 64, 128, 128 | 64)),
                        value_name='OutpointFlag(...)')

                    tx.input_outpoint_flag[index] = outpoint_flag

                outpoint_hash = tx.input_outpoint_hash.get_known(index)
                if not outpoint_hash:
                    outpoint_hash = SymData(name='INPUT_%_OUTPOINT_HASH',
                                            args=(bn,), possible_sizes=(32,))
                    outpoint_hash.use_as_ByteSeq()
                    tx.input_outpoint_hash[index] = outpoint_hash

                z3check()

                refcount_neighbors(outpoint_hash, prevout_n, outpoint_flag,
                                   args=(bn,))

                popstack()
                push(outpoint_hash)
                push(prevout_n)
                push(outpoint_flag)

            elif op == OP_INSPECTINPUTASSET:

                asset = tx.input_asset.get_known(index)
                if not asset:
                    asset = SymData(name='INPUT_%_ASSET', args=(bn,))
                    asset.use_as_ByteSeq()
                    asset.set_possible_sizes(32, value_name='Asset(...)')
                    tx.input_asset[index] = asset

                pfx = tx.input_asset_prefix.get_known(index)
                if not pfx:
                    pfx = SymData(name='INPUT_%_ASSET_PREFIX', args=(bn,))
                    pfx.use_as_ByteSeq()
                    pfx.set_possible_values(*(bytes([v]) for v in (1, 10, 11)),
                                            value_name='AssetPrefix(...)')
                    tx.input_asset_prefix[index] = pfx

                z3check()

                refcount_neighbors(asset, pfx, args=(bn,))

                popstack()
                push(asset)
                push(pfx)

            elif op == OP_INSPECTINPUTVALUE:

                value = tx.input_value.get_known(index)
                got_value = bool(value)
                if not value:
                    value = SymData(name='INPUT_%_VALUE', args=(bn,),
                                    possible_sizes=(8, 32))
                    value.use_as_ByteSeq()
                    tx.input_value[index] = value

                pfx = tx.input_value_prefix.get_known(index)
                got_pfx = bool(pfx)
                if not pfx:
                    pfx = SymData(name='INPUT_%_VALUE_PREFIX', args=(bn,))
                    pfx.use_as_ByteSeq()
                    tx.input_value_prefix[index] = pfx

                if got_value:
                    assert got_pfx
                else:
                    assert not got_pfx
                    add_amount_constraints(prefix=pfx, value=value)

                    # There are no spendable 0-value outputs
                    Check(Implies(pfx.as_ByteSeq()[0] == 1,
                                  value.as_ByteSeq() != IntSeqVal(b'\x00'*8)))

                z3check()

                refcount_neighbors(value, pfx, args=(bn,))

                popstack()
                push(value)
                push(pfx)

            elif op == OP_INSPECTINPUTSCRIPTPUBKEY:

                witprog = tx.input_scriptpubkey_witprog.get_known(index)
                got_witprog = bool(witprog)
                if not witprog:
                    witprog = SymData(name='INPUT_%_SPK_WITPROG', args=(bn,))
                    witprog.use_as_ByteSeq()
                    tx.input_scriptpubkey_witprog[index] = witprog

                witver = tx.input_scriptpubkey_witver.get_known(index)
                got_witver = bool(witver)
                if not witver:
                    witver = SymData(name='INPUT_%_SPK_WITVER', args=(bn,))
                    witver.use_as_ByteSeq()
                    tx.input_scriptpubkey_witver[index] = witver

                if got_witprog:
                    assert got_witver
                else:
                    assert not got_witver
                    add_scriptpubkey_constraints(witver=witver, witprog=witprog)

                z3check()

                refcount_neighbors(witprog, witver, args=(bn,))

                popstack()
                push(witprog)
                push(witver)

            elif op == OP_INSPECTINPUTSEQUENCE:

                nSequence = tx.nSequence.get_known(index)
                if not nSequence:
                    nSequence = SymData(name='INPUT_%_SEQUENCE', args=(bn,))
                    nSequence.set_possible_sizes(4, value_name='LE32(...)')
                    nSequence.use_as_ByteSeq()
                    tx.nSequence[index] = nSequence

                z3check()

                popstack()
                push(nSequence)

            elif op == OP_INSPECTINPUTISSUANCE:

                infkeys = tx.issuance_inflationkeys.get_known(index)
                infk_pfx = tx.issuance_inflationkeys_prefix.get_known(index)
                iamount = tx.issuance_amount.get_known(index)
                iamount_pfx = tx.issuance_amount_prefix.get_known(index)
                asset_blinding_nonce = tx.issuance_asset_blinding_nonce.get_known(index)
                asset_entropy = tx.issuance_asset_entropy.get_known(index)

                gotflags = (bool(infkeys), bool(infk_pfx),
                            bool(iamount), bool(iamount_pfx),
                            bool(asset_blinding_nonce), bool(asset_entropy))

                if all(gotflags):
                    pass
                else:
                    assert not any(gotflags)

                    infkeys = SymData(name='INPUT_%_ISSUANCE_INFLATIONKEYS',
                                      args=(bn,), possible_sizes=(8, 32))
                    infk_pfx = SymData(name='INPUT_%_ISSUANCE_INFLATIONKEYS_PREFIX',
                                       args=(bn,))
                    iamount = SymData(name='INPUT_%_ISSUANCE_AMOUNT', args=(bn,),
                                      possible_sizes=(8, 32))
                    iamount_pfx = SymData(name='INPUT_%_ISSUANCE_AMOUNT_PREFIX',
                                          args=(bn,))
                    asset_blinding_nonce = SymData(
                        name='INPUT_%_ISSUANCE_ASSETBLINDINGNONCE', args=(bn,),
                        possible_sizes=(32,))
                    asset_entropy = SymData(name='INPUT_%_ISSUANCE_ASSETENTROPY',
                                            args=(bn,))
                    asset_entropy.set_possible_sizes(32, value_name='AssetEntropy(...)')

                    infkeys.use_as_ByteSeq()
                    infk_pfx.use_as_ByteSeq()
                    iamount.use_as_ByteSeq()
                    iamount_pfx.use_as_ByteSeq()
                    asset_blinding_nonce.use_as_ByteSeq()
                    asset_entropy.use_as_ByteSeq()

                    tx.issuance_inflationkeys[index] = infkeys
                    tx.issuance_inflationkeys_prefix[index] = infk_pfx
                    tx.issuance_amount[index] = iamount
                    tx.issuance_amount_prefix[index] = iamount_pfx
                    tx.issuance_asset_blinding_nonce[index] = asset_blinding_nonce
                    tx.issuance_asset_entropy[index] = asset_entropy

                    add_amount_constraints(prefix=infk_pfx, value=infkeys)
                    add_amount_constraints(prefix=iamount_pfx, value=iamount)

                    bytes_int64_zero = IntSeqVal(b'\x00'*8)
                    # In a non-null assetissuance, either inflation keys are
                    # non-null, or issuance amount is non-null, or both
                    Check(Implies(And(iamount_pfx.as_ByteSeq()[0] == 1,
                                      iamount.as_ByteSeq() == bytes_int64_zero),
                                  Or(infk_pfx.as_ByteSeq()[0] != 1,
                                     infkeys.as_ByteSeq() != bytes_int64_zero)))
                    Check(Implies(And(infk_pfx.as_ByteSeq()[0] == 1,
                                      infkeys.as_ByteSeq() == bytes_int64_zero),
                                  Or(iamount_pfx.as_ByteSeq()[0] != 1,
                                     iamount.as_ByteSeq() != bytes_int64_zero)))

                    # Only initial issuance can have reissuance tokens
                    Check(Implies(And(infk_pfx.as_ByteSeq()[0] == 1,
                                      infkeys.as_ByteSeq() == bytes_int64_zero),
                                  asset_blinding_nonce.as_ByteSeq()
                                  == IntSeqVal(b'\x00'*32)))

                    if not should_skip_immediately_failed_branch():
                        new_context = ctx.branch(
                            cond=bn,
                            cond_designations=('Has issuance', 'No issuance'))
                        fflag = SymData(name=f'{op.name}_FAILURE_FLAG')
                        fflag.use_as_Int()
                        new_context.run_on_start(lambda: new_context.push(fflag))
                        new_context.run_on_start(
                            lambda: Check(fflag.as_Int() == 0, err_branch_condition_invalid(),
                                          enforcement_condition=fflag))
                        new_context.run_on_start(lambda: fflag.set_known_bool(False, set_size=True))

                z3check()

                popstack()

                assert infkeys
                assert infk_pfx
                assert iamount
                assert iamount_pfx
                assert asset_entropy
                assert asset_blinding_nonce

                refcount_neighbors(infkeys, infk_pfx, iamount, iamount_pfx,
                                   asset_entropy, asset_blinding_nonce,
                                   args=(bn,))

                push(infkeys)
                push(infk_pfx)
                push(iamount)
                push(iamount_pfx)
                push(asset_entropy)
                push(asset_blinding_nonce)

            else:
                raise AssertionError(f'unexpected opcode {op.name}')

        scope()
    elif op == OP_PUSHCURRENTINPUTINDEX:

        push(tx.current_input_index)

    elif op in (OP_INSPECTOUTPUTASSET, OP_INSPECTOUTPUTVALUE,
                OP_INSPECTOUTPUTNONCE, OP_INSPECTOUTPUTSCRIPTPUBKEY):
        def scope() -> None:
            bn = stacktop(-1)

            index = bn.use_as_Int()

            Check(index >= 0, err_negative_argument())

            if isinstance(index, int):
                if index >= env.max_num_outputs:
                    raise ScriptFailure(f'{op.name}: index too big')

            Check(index < tx.num_outputs.as_Int(),
                  err_argument_above_bounds())

            if op == OP_INSPECTOUTPUTASSET:

                asset = tx.output_asset.get_known(index)
                if not asset:
                    asset = SymData(name='OUTPUT_%_ASSET', args=(bn,))
                    asset.use_as_ByteSeq()
                    asset.set_possible_sizes(32, value_name='Asset(...)')
                    tx.output_asset[index] = asset

                pfx = tx.output_asset_prefix.get_known(index)
                if not pfx:
                    pfx = SymData(name='OUTPUT_%_ASSET_PREFIX', args=(bn,))
                    pfx.use_as_ByteSeq()
                    pfx.set_possible_values(*(bytes([v]) for v in (1, 10, 11)),
                                            value_name='AssetPrefix(...)')
                    tx.output_asset_prefix[index] = pfx

                z3check()

                refcount_neighbors(asset, pfx, args=(bn,))

                popstack()
                push(asset)
                push(pfx)

            elif op == OP_INSPECTOUTPUTVALUE:

                value = tx.output_value.get_known(index)
                got_value = bool(value)
                if not value:
                    value = SymData(name='OUTPUT_%_VALUE', args=(bn,),
                                    possible_sizes=(8, 32))
                    value.use_as_ByteSeq()
                    tx.output_value[index] = value

                pfx = tx.output_value_prefix.get_known(index)
                got_pfx = bool(pfx)
                if not pfx:
                    pfx = SymData(name='OUTPUT_%_VALUE_PREFIX', args=(bn,))
                    pfx.use_as_ByteSeq()
                    tx.output_value_prefix[index] = pfx

                if got_value:
                    assert got_pfx
                else:
                    assert not got_pfx
                    add_amount_constraints(prefix=pfx, value=value)

                    # There are no spendable 0-value outputs.
                    # 0x6a is OP_RETURN.
                    # zero-length witprog is fee output in elements
                    out_witprog = tx.output_scriptpubkey_witprog.as_ref(index)
                    out_witver = tx.output_scriptpubkey_witver.as_ref(index)
                    op_return_hash = hashlib.sha256(b'\x6a').digest()
                    Check(Implies(And(pfx.as_ByteSeq()[0] == 1,
                                      value.as_ByteSeq() == IntSeqVal(b'\x00'*8)),
                                  Or(And(out_witver[0] == 0x81,  # -1
                                         out_witprog == IntSeqVal(op_return_hash)),
                                     Length(out_witprog) > MAX_SCRIPT_SIZE,
                                     Length(out_witprog) == 0)))

                z3check()

                refcount_neighbors(value, pfx, args=(bn,))

                popstack()
                push(value)
                push(pfx)

            elif op == OP_INSPECTOUTPUTNONCE:

                nonce = tx.output_nonce.get_known(index)
                if not nonce:
                    nonce = SymData(name='OUTPUT_%_NONCE', args=(bn,))
                    nonce.set_possible_sizes(0, 33, value_name='OutputNonce(...)')
                    nonce.use_as_ByteSeq()
                    tx.output_nonce[index] = nonce

                Check(Or(nonce.Length() == 0,
                         And(nonce.Length() == 33,
                             Or(nonce.as_ByteSeq()[0] == 1,
                                nonce.as_ByteSeq()[0] == 2,
                                nonce.as_ByteSeq()[0] == 3))))

                z3check()

                popstack()
                push(nonce)

            elif op == OP_INSPECTOUTPUTSCRIPTPUBKEY:

                witprog = tx.output_scriptpubkey_witprog.get_known(index)
                got_witprog = bool(witprog)
                if not witprog:
                    witprog = SymData(name='OUTPUT_%_SPK_WITPROG', args=(bn,))
                    witprog.use_as_ByteSeq()
                    tx.output_scriptpubkey_witprog[index] = witprog

                witver = tx.output_scriptpubkey_witver.get_known(index)
                got_witver = bool(witver)
                if not witver:
                    witver = SymData(name='OUTPUT_%_SPK_WITVER', args=(bn,))
                    witver.use_as_ByteSeq()
                    tx.output_scriptpubkey_witver[index] = witver

                if got_witprog:
                    assert got_witver
                else:
                    assert not got_witver
                    add_scriptpubkey_constraints(witver=witver, witprog=witprog)

                z3check()

                refcount_neighbors(witprog, witver, args=(bn,))

                popstack()
                push(witprog)
                push(witver)

            else:
                raise AssertionError(f'unexpected opcode {op.name}')

        scope()
    elif op == OP_INSPECTVERSION:

        push(tx.nVersion)

    elif op == OP_INSPECTLOCKTIME:

        push(tx.nLockTime)

    elif op == OP_INSPECTNUMINPUTS:

        push(tx.num_inputs)

    elif op == OP_INSPECTNUMOUTPUTS:

        push(tx.num_outputs)

    elif op == OP_TXWEIGHT:

        push(tx.weight)

    elif op in (OP_ADD64, OP_SUB64, OP_MUL64):
        def scope() -> None:
            vcha = stacktop64(-2)
            vchb = stacktop64(-1)

            if op in (OP_ADD64, OP_MUL64):
                r = symresult(op, *maybe_sort_args(vcha, vchb))
            else:
                r = symresult(op, vcha, vchb)

            r_sf = sym_successflag(op, vcha, vchb)

            op_table: dict[OpCode, Callable[[Union[int, 'z3.ArithRef'],
                                             Union[int, 'z3.ArithRef']],
                                            Union[int, 'z3.ArithRef']]] = \
                {
                    OP_ADD64: lambda a, b: a + b,
                    OP_SUB64: lambda a, b: a - b,
                    OP_MUL64: lambda a, b: a * b,
                }

            a = vcha.as_Int64()
            b = vchb.as_Int64()

            if op == OP_ADD64:
                args_invalid = Or(And(a > 0, b > IntLE64.MAX_VALUE - a),
                                  And(a < 0, b < IntLE64.MIN_VALUE - a))
            elif op == OP_SUB64:
                args_invalid = Or(And(b > 0, a < IntLE64.MIN_VALUE + b),
                                  And(b < 0, a > IntLE64.MAX_VALUE + b))
            elif op == OP_MUL64:
                if (isinstance(a, int) and a == 0) or \
                        (isinstance(b, int) and b == 0):
                    args_invalid = False
                else:
                    def divide(mv: int, v: Union[int, 'z3.ArithRef']
                               ) -> Union[int, 'z3.ArithRef']:
                        if isinstance(v, int):
                            return mv // v

                        return mv / v

                    args_invalid = Or(
                        And(a > 0, b > 0, a > divide(IntLE64.MAX_VALUE, b)),
                        And(a > 0, b < 0, b < divide(IntLE64.MIN_VALUE, a)),
                        And(a < 0, b > 0, a < divide(IntLE64.MIN_VALUE, b)),
                        And(a < 0, b < 0, b < divide(IntLE64.MAX_VALUE, a)))
            else:
                assert False, op

            r_sf.set_as_Int(If(args_invalid, 0, 1))

            if not should_skip_immediately_failed_branch():
                new_context = ctx.branch(
                    cond=(vcha, vchb),
                    cond_designations=('Success branch', 'Failure branch'))
                new_context.run_on_start(lambda: new_context.push(r_sf))
                new_context.run_on_start(
                    lambda: Check(r_sf.as_Int() == 0, err_branch_condition_invalid(),
                                  enforcement_condition=r_sf))
                new_context.run_on_start(lambda: r_sf.set_known_bool(False, set_size=True))

            Check(r_sf.as_Int() == 1, err_invalid_arguments(),
                  enforcement_condition=r_sf)
            r_sf.set_known_bool(True, set_size=True)

            r.set_as_Int64(op_table[op](vcha.as_Int64(), vchb.as_Int64()))

            z3check()

            popstack()
            popstack()

            push(r)
            push(r_sf)

        scope()
    elif op == OP_DIV64:
        def scope() -> None:
            vcha = stacktop64(-2)
            vchb = stacktop64(-1)

            a = vcha.as_Int64()
            b = vchb.as_Int64()

            res = symresult(op, vcha, vchb)

            res_sf = sym_successflag(op, vcha, vchb)

            rem = SymData(name='REMAINDER', args=(res,))
            qt = SymData(name='QUOTIENT', args=(res,))

            args_invalid = Or(b == 0, And(b == -1, a == IntLE64.MIN_VALUE))

            res_sf.set_as_Int(If(args_invalid, 0, 1))

            if not should_skip_immediately_failed_branch():
                new_context = ctx.branch(
                    cond=(vcha, vchb),
                    cond_designations=('Success branch', 'Failure branch'))
                new_context.run_on_start(lambda: new_context.push(res_sf))
                new_context.run_on_start(
                    lambda: Check(res_sf.as_Int() == 0, err_branch_condition_invalid(),
                                  enforcement_condition=res_sf))
                new_context.run_on_start(lambda: res_sf.set_known_bool(False, set_size=True))

            Check(res_sf.as_Int() == 1, err_invalid_arguments(),
                  enforcement_condition=res_sf)
            res_sf.set_known_bool(True, set_size=True)

            if isinstance(a, int) and isinstance(b, int):
                r_i64 = a % b
                q_i64 = a // b
                if (r_i64 < 0 and b > 0):
                    # ensures that 0<=r<|b|
                    r_i64 += b
                    q_i64 -= 1
                elif (r_i64 < 0 and b < 0):
                    # ensures that 0<=r<|b|
                    r_i64 -= b
                    q_i64 += 1

                rem.set_static(IntLE64.from_int(r_i64))
                qt.set_static(IntLE64.from_int(q_i64))
            else:
                rem.use_as_Int64()
                qt.use_as_Int64()

                r = a % b
                q = a / b
                Check(rem.as_Int64()
                      == If(And(r < 0, b > 0),
                            r + b, If(And(r < 0, b < 0), r - b, r)))
                Check(qt.as_Int64()
                      == If(And(r < 0, b > 0),
                            q - 1, If(And(r < 0, b < 0), q + 1, q)))

            z3check()

            refcount_neighbors(rem, qt, res_sf)

            popstack()
            popstack()
            push(rem)
            push(qt)
            push(res_sf)

        scope()
    elif op in (OP_LESSTHAN64, OP_LESSTHANOREQUAL64, OP_GREATERTHAN64,
                OP_GREATERTHANOREQUAL64):
        def scope() -> None:
            vcha = stacktop64(-2)
            vchb = stacktop64(-1)

            r = symresult(op, vcha, vchb)

            op_table: dict[OpCode, Callable[[Union[int, 'z3.ArithRef'],
                                             Union[int, 'z3.ArithRef']],
                                            Union[int, 'z3.ArithRef']]] = \
                {
                    OP_LESSTHAN64:           lambda a, b: a < b,
                    OP_LESSTHANOREQUAL64:    lambda a, b: a <= b,
                    OP_GREATERTHAN64:        lambda a, b: a > b,
                    OP_GREATERTHANOREQUAL64: lambda a, b: a >= b,
                }

            r.set_as_Int(If(op_table[op](vcha.as_Int64(), vchb.as_Int64()),
                            1, 0))

            z3check()

            popstack()
            popstack()

            push(r)
        scope()
    elif op == OP_NEG64:
        def scope() -> None:
            vcha = stacktop64(-1)

            r = symresult(op, vcha)
            r_sf = sym_successflag(op, vcha)

            args_invalid = vcha.as_Int64() == IntLE64.MIN_VALUE

            r_sf.set_as_Int(If(args_invalid, 0, 1))

            if not should_skip_immediately_failed_branch():
                new_context = ctx.branch(
                    cond=vcha,
                    cond_designations=('Success branch', 'Failure branch'))
                new_context.run_on_start(lambda: new_context.push(r_sf))
                new_context.run_on_start(
                    lambda: Check(r_sf.as_Int() == 0, err_branch_condition_invalid(),
                                  enforcement_condition=r_sf))
                new_context.run_on_start(lambda: r_sf.set_known_bool(False, set_size=True))

            Check(r_sf.as_Int() == 1, err_invalid_arguments(),
                  enforcement_condition=r_sf)
            r_sf.set_known_bool(True, set_size=True)

            r.set_as_Int64(-vcha.as_Int64())

            z3check()

            popstack()
            push(r)
            push(r_sf)

        scope()
    elif op == OP_SCRIPTNUMTOLE64:
        def scope() -> None:
            bn = stacktop(-1)
            r = symresult(op, bn)

            r.set_as_Int64(bn.use_as_Int())

            z3check()

            popstack()
            push(r)

        scope()
    elif op == OP_LE64TOSCRIPTNUM:
        def scope() -> None:
            bn = stacktop64(-1)

            r = symresult(op, bn)

            value = bn.as_Int64()

            Check(And(value >= MIN_SCRIPTNUM_INT, value <= MAX_SCRIPTNUM_INT),
                  err_scriptnum_out_of_bounds())

            r.set_as_Int(value)

            z3check()

            popstack()
            push(r)

        scope()
    elif op == OP_LE32TOLE64:
        def scope() -> None:
            vch = stacktop(-1)

            r = symresult(op, vch)

            if vch.is_static:
                if len(vch.as_bytes()) != 4:
                    raise ScriptFailure(f'{op.name}: expected 4 bytes as argument')

                r.set_static(
                    IntLE64.from_int(struct.unpack('<i', vch.as_bytes())[0]))
            else:
                le32_unsigned_to_integer(vch.use_as_ByteSeq(), r.use_as_Int64())

            z3check()

            popstack()
            push(r)

        scope()
    elif op == OP_ECMULSCALARVERIFY:
        def scope() -> None:
            vchRes = stacktop(-3)
            vchGenerator = stacktop(-2)
            vchScalar = stacktop(-1)

            b_res = vchRes.use_as_ByteSeq()
            b_gen = vchGenerator.use_as_ByteSeq()
            b_scalar = vchScalar.use_as_ByteSeq()

            Check(vchGenerator.Length() == 33, err_invalid_pubkey_length())
            Check(vchRes.Length() == 33, err_invalid_pubkey_length())
            Check(vchScalar.Length() == 32, err_invalid_scalar_length())

            r = SymData(name=op.name, args=(vchRes, vchGenerator, vchScalar))
            r.use_as_Int()
            r.set_possible_values(0, 1)

            if vchRes.is_static:
                if not is_static_pubkey_valid(vchGenerator.as_bytes()):
                    r.set_static(0)

                if not is_static_pubkey_valid(vchRes.as_bytes()):
                    r.set_static(0)
            else:
                Check(Implies(Not(Or(b_gen[0] == 2, b_gen[0] == 3)),
                              r.as_Int() == 0))
                Check(Implies(Not(Or(b_res[0] == 2, b_res[0] == 3)),
                              r.as_Int() == 0))

            ec_mul_scalar = env.get_sym_ec_mul_scalar_fun()
            Check(b_res == ec_mul_scalar(b_gen, b_scalar),
                  err_known_args_different_result())

            if env.z3_enabled:
                seq_a = FreshConst(IntSeqSortRef(), 'seq_a')
                seq_b = FreshConst(IntSeqSortRef(), 'seq_b')
                Check(z3.ForAll(
                    [seq_a, seq_b],
                    Implies(b_res == ec_mul_scalar(seq_a, seq_b),
                            And(seq_a == b_gen, seq_b == b_scalar))),
                    err_known_result_different_args())

            Check(r.as_Int() != 0, err_ecmultverify(),
                  enforcement_condition=r)

            z3check()

            ctx.add_enforcement(r)

            popstack()
            popstack()
            popstack()

        scope()
    elif op == OP_TWEAKVERIFY:
        def scope() -> None:
            vchTweakedKey = stacktop(-3)
            vchTweak = stacktop(-2)
            vchInternalKey = stacktop(-1)

            b_tw_key = vchTweakedKey.use_as_ByteSeq()
            b_tweak = vchTweak.use_as_ByteSeq()
            b_int_key = vchInternalKey.use_as_ByteSeq()

            r = SymData(name=op.name,
                        args=(vchTweakedKey, vchTweak, vchInternalKey))
            r.use_as_Int()
            r.set_possible_values(0, 1)

            Check(vchTweakedKey.Length() == 33, err_invalid_pubkey_length())
            Check(Or(b_tw_key[0] == 2, b_tw_key[0] == 3), err_invalid_pubkey())

            if vchTweakedKey.is_static:
                if not is_static_pubkey_valid(vchTweakedKey.as_bytes()):
                    r.set_static(0)

            add_xonly_pubkey_constraints(vchInternalKey,
                                         for_signature_check=False)

            Check(vchTweak.Length() == 32, err_invalid_scalar_length())

            ec_tweak_add = env.get_sym_ec_tweak_add_fun()

            Check(b_tw_key == ec_tweak_add(b_int_key, b_tweak),
                  err_known_args_different_result())

            if env.z3_enabled:
                seq_a = FreshConst(IntSeqSortRef(), 'seq_a')
                seq_b = FreshConst(IntSeqSortRef(), 'seq_b')
                Check(z3.ForAll(
                    [seq_a, seq_b],
                    Implies(b_tw_key == ec_tweak_add(seq_a, seq_b),
                            And(seq_a == b_int_key, seq_b == b_tweak))),
                    err_known_result_different_args())

            Check(r.as_Int() != 0, err_tweakverify(),
                  enforcement_condition=r)

            z3check()

            ctx.add_enforcement(r)

            popstack()
            popstack()
            popstack()

        scope()
    else:
        for plugin in env.get_loaded_op_plugins():
            phf = PluginHelperFunctions(
                stacktop=stacktop, stacktop64=stacktop64,
                push=push, popstack=popstack, erase=erase)

            if plugin.exec_opcode(ctx, env, op, phf):
                break
        else:
            raise ScriptFailure(f'unhandled opcode: {op}')

    combined_stack_len = len(ctx.stack) + len(ctx.altstack)
    if combined_stack_len > MAX_STACK_SIZE:
        raise ScriptFailure(
            f'stack overflow, stack len {len(ctx.stack)}, '
            f'altstack len {len(ctx.altstack)}')

    if combined_stack_len > ctx.max_combined_stack_len:
        ctx.num_expunged_witnesses = max(
            ctx.num_expunged_witnesses,
            combined_stack_len - len(ctx.used_witnesses)
        )
        ctx.max_combined_stack_len = combined_stack_len

    for val in popped_or_erased_values:
        if val.refcount == 0:
            neighbors = val.get_refcount_neighbors()
            if not any(nb.refcount > 0 for nb in neighbors):
                for nb in neighbors:
                    ctx.unused_values.add(nb)

    return True


def symex_script() -> None:  # noqa

    env = cur_env()

    def symex_context(ctx: ExecContext) -> None:

        global g_stack_symdata_index
        global g_var_save_positions

        if ctx.is_finalized:
            return

        if env.log_solving_attempts:
            env.solving_log_ensure_empty_line()
            env.solving_log(
                f'Analyzing from position {op_pos_info(max(0, ctx.pc-1))}')
            env.solving_log_ensure_empty_line()

        z3_push_context()

        g_stack_symdata_index = 0

        ctx.on_start()

        while ctx.pc < len(g_script_body) and not ctx.failure:

            pre_op_state = ctx.exec_state.clone()
            op_or_sd = g_script_body[ctx.pc]

            if env.sigversion in (SigVersion.BASE, SigVersion.WITNESS_V0) and \
                    isinstance(op_or_sd, OpCode) and \
                    op_or_sd.code > OP_16.code:

                ctx.segwit_mode_op_count += 1
                if ctx.segwit_mode_op_count > MAX_OPS_PER_SCRIPT_SEGWIT_MODE:
                    ctx.register_failure(
                        ctx.pc, 'Maximum opcode count is reached')
                    break

            num_pre_op_used_witnesses = len(ctx.used_witnesses)

            if symex_op(ctx, op_or_sd):
                if data_reference := g_var_save_positions.get(ctx.pc):
                    if len(ctx.stack) > 0:
                        ctx.stack[-1].set_data_reference(data_reference)

                num_new_witnesses = len(ctx.used_witnesses) - num_pre_op_used_witnesses
                assert num_new_witnesses >= 0
                if num_new_witnesses:
                    for wit in ctx.used_witnesses[-num_new_witnesses:]:
                        pre_op_state.stack.insert(0, wit)

                ctx.exec_state_log[ctx.pc] = pre_op_state

            if not ctx.failure:
                ctx.pc += 1

            g_stack_symdata_index = 0

        if not ctx.failure:
            ctx.exec_state_log[ctx.pc] = ctx.exec_state.clone()
            with CurrentOp(None):
                finalize(ctx)

        g_stack_symdata_index = None

        z3_pop_context()

    env.get_root_branch().walk_contexts(symex_context, is_executing=True)


def get_opcodes(script_lines: Iterable[str],    # noqa
                allow_nonstandard_size_scriptnums: bool = False
                ) -> tuple[tuple[OpCode | ScriptData, ...],
                           list[int], dict[int, str]]:

    env = cur_env()

    opcodes: list[OpCode | ScriptData] = []
    line_no_table: list[int] = []
    var_save_positions: dict[int, str] = {}

    seen_data_reference_names: dict[str, int] = {}

    line_no = -1

    for l_idx, line in enumerate(script_lines):

        line_no = l_idx + 1

        def die(msg: str) -> NoReturn:
            msg = re.sub('[\\x00-\x1F]', '?', msg)
            sys.stderr.write(f'ERROR at line {line_no}: {msg}\n')
            sys.exit(-1)

        data_reference = ''
        # remove '//' comments
        if m := re.search('//', line):
            comment = line[m.end():]
            line = line[:m.start()]
            if m := re.match('\\s*=>(\\S+)', comment):
                data_reference = m.group(1)

        for op_str in line.split():
            got_angle_brackets = False
            if op_str.startswith('<') and op_str.endswith('>'):
                op_str = op_str[1:-1]
                got_angle_brackets = True

            op: OpCode | ScriptData
            if op_str.startswith('$') and op_str[1:].isidentifier():
                op = ScriptData(name=op_str, value=None)
            elif len(op_str) >= 2 and op_str[0] == "'" and op_str[-1] == "'":
                if "'" in op_str[1:-1]:
                    die('ambiguous quotes. you have to use hex encoding '
                        'if you want to include single quote (0x27) in data')

                op = ScriptData(name=None, value=op_str[1:-1],
                                do_check_non_minimal=env.minimaldata_flag_strict)
            elif (env.is_elements and
                  op_str.lower().startswith('le64(') and op_str.endswith(')')):

                op_str = op_str[5:-1]

                sign = 1
                if op_str.startswith('-'):
                    sign = -1
                    op_str = op_str[1:]

                if not op_str.isdigit():
                    die('incorrect argument to le64()')

                if op_str.startswith('0') and len(op_str) > 1:
                    die('no leading zeroes allowed')

                v = int(op_str)*sign
                op = ScriptData(name=None, value=IntLE64.from_int(v))

            elif (op_str.isdigit() or (op_str.startswith('-')
                                       and op_str[1:].isdigit())):
                sign = 1
                if op_str.startswith('-'):
                    sign = -1
                    op_str = op_str[1:]
                if op_str.startswith('0') and len(op_str) > 1:
                    die('no leading zeroes allowed')

                v = int(op_str)*sign

                if not allow_nonstandard_size_scriptnums:
                    vch = integer_to_scriptnum(v)
                    if len(vch) > SCRIPTNUM_DEFAULT_SIZE:
                        die(f'the number {v}, when converted to '
                            f'CScriptNum will be {len(vch)} bytes in length, '
                            f'which is above the limit of '
                            f'{SCRIPTNUM_DEFAULT_SIZE} bytes')

                op = ScriptData(name=None, value=v)

            elif op_str.lower().startswith("x('") and op_str.endswith("')"):
                data_str = op_str[3:-2]
                try:
                    op = ScriptData(
                        name=None, value=bytes.fromhex(data_str),
                        do_check_non_minimal=env.minimaldata_flag_strict)
                except ValueError:
                    die(f'cannot decode data: {data_str}')
            elif op_str.lower().startswith("0x"):
                data_str = op_str[2:]
                try:
                    op = ScriptData(
                        name=None, value=bytes.fromhex(data_str),
                        do_check_non_minimal=env.minimaldata_flag_strict)
                except ValueError:
                    die(f'cannot decode data: {data_str}')
            elif got_angle_brackets:
                die(f'unexpected value in angle brackets: {op_str}')
            else:
                op_str = op_str.upper()
                if op_str.startswith('OP_'):
                    maybe_op = _OP_TABLE.get(op_str[3:])
                else:
                    maybe_op = _OP_TABLE.get(op_str)

                if maybe_op is None:
                    die(f'unknown opcode {op_str}')

                op = maybe_op

                mode = 'elements' if env.is_elements else 'bitcoin'
                if env.sigversion == SigVersion.TAPSCRIPT:
                    mode = f'{mode} (tapscript)'
                else:
                    mode = f'{mode} (non-tapscript)'

                if op not in env.get_enabled_opcodes():
                    die(f'opcode {op_str} is not valid for {mode}')

            line_no_table.append(line_no)
            opcodes.append(op)

        if data_reference and env.restrict_data_reference_names:
            if data_reference and not data_reference.isidentifier():
                sys.stderr.write(
                    f"NOTE: non-identifier data_reference is ignored on input line "
                    f"{line_no}\n")
                data_reference = ''

        if data_reference:
            if data_reference in seen_data_reference_names:
                die(f'data_reference at line {line_no} was already used at line '
                    f'{seen_data_reference_names[data_reference]}')

            if "'" in data_reference:
                die("apostrophe <<'>> is not allowed in data reference names")

            seen_data_reference_names[data_reference] = line_no

            var_save_positions[len(opcodes)-1] = data_reference

    line_no_table.append(line_no+1)

    return tuple(opcodes), line_no_table, var_save_positions

def finalize(ctx: ExecContext) -> None:  # noqa
    assert not ctx.failure
    assert ctx.pc == len(g_script_body)

    try:
        _finalize(ctx)
    except ScriptFailure as sf:
        ctx.register_failure(ctx.pc, str(sf))

    ctx.is_finalized = True


def _finalize(ctx: ExecContext) -> None:  # noqa
    env = cur_env()
    assert not ctx.failure
    assert ctx.pc == len(g_script_body)

    env.solving_log_ensure_empty_line()

    if ctx.altstack:
        ctx.add_warning(f'Altstack length is {len(ctx.altstack)}')

    if ctx.vfExec:
        raise ScriptFailure('unbalanced conditional (on end of script)')

    top: SymData | None = None

    if not env.is_incomplete_script:
        top = ctx.stacktop(-1)

        if top._wit_no is not None:
            ctx.add_warning(
                f'Stack execution result '
                f'(argument for final implied VERIFY) '
                f'comes directly from witness "{top.name}"')

        if top.is_static:
            if not top.as_bool():
                raise ScriptFailure(
                    'top of stack is always False after script end')

        Check(use_as_script_bool(top) != 0, err_final_verify(),
              enforcement_condition=top)

        if top:
            ctx.add_enforcement(top, is_script_bool=True)

    for sd in ctx.sym_depth_register:
        sd_bytes = integer_to_scriptnum(sd.depth)
        if cv := sd.get_constrained_value():
            if sd.pc_of_last_static_update is None:
                failure_pc = ctx.pc
            else:
                failure_pc = sd.pc_of_last_static_update

            pvals = cv.possible_values
            if pvals and sd_bytes not in pvals:
                ctx.register_failure(
                    failure_pc,
                    'final depth is not '
                    + ('within possible values' if len(pvals) > 1
                       else 'equal to static value')
                    + 'that was set')
                return

            psizes = cv.possible_sizes
            if psizes and len(sd_bytes) not in psizes:
                ctx.register_failure(
                    failure_pc,
                    'final depth bytesize is not within possible sizes that was set')
                return

        Check(sd.use_as_Int() == sd.depth)

    mvdict_req: dict[str, tuple[str, SymDataRType]] = {}
    mvnamemap: dict[str, 'SymData'] = {}
    if env.produce_model_values:
        for wit in ctx.used_witnesses:
            wit.update_model_values_request_dict(mvdict_req, mvnamemap)

        processed = ctx.used_witnesses.copy()

        for txval in ctx.tx.values():
            assert txval not in processed, \
                ("only witnesses are processed at this point, tx values"
                    "cannot intersect")
            txval.update_model_values_request_dict(mvdict_req, mvnamemap)
            processed.append(txval)

        for val in g_data_placeholders.values():
            if val not in processed:
                val.update_model_values_request_dict(mvdict_req, mvnamemap)
                processed.append(val)

        for val in ctx.stack:
            if val not in processed:
                val.update_model_values_request_dict(mvdict_req, mvnamemap)
                processed.append(val)

    if env.log_progress:
        print_as_header("Finalizing path", is_solving=True)
        print_as_header(ctx.get_timeline_strings() or ["[Root]"],
                        level=1, is_solving=True, no_empty_line_above=True)

    try:
        mvdict = z3check(force_check=True,
                         model_values_to_retrieve=mvdict_req)
    except ScriptFailure as sf:
        if env.log_progress:
            env.ensure_empty_line()
            env.write("Failed final checks")
            env.ensure_empty_line()

        raise sf

    if not env.is_incomplete_script:
        assert len(ctx.stack) > 0

    if len(ctx.stack) > 1:
        if not env.cleanstack_flag:
            if not env.is_incomplete_script:
                ctx.add_warning(
                    f'Script ends with stack length {len(ctx.stack)}')
        else:
            raise ScriptFailure(
                f'Cleanstack rule fail on script end, '
                f'stack lengh is {len(ctx.stack)}')

    maybe_report_elapsed_time()

    env.solving_log_ensure_empty_line()

    if env.produce_model_values:
        mvdict = mvdict or {}
        for name, val in mvnamemap.items():
            val.set_model_value(mvdict.get(name))

    if env.log_progress and ctx.z3_warning_vars:
        print_as_header('Checking for possible warnings', level=2,
                        is_solving=True)

    for pc, ww in ctx.z3_warning_vars:
        if is_cond_possible(ww.as_Int() == 1, ww,
                            name=f'{ww.name} @ {op_pos_info(pc)}',
                            fail_msg='  - not possible'):
            assert ww.name
            ctx.warnings.append((pc, ww.name))

    verify_targets: list[Enforcement] = []
    if not env.use_z3_incremental_mode:
        for e in ctx.enforcements:
            if e.pc >= len(g_script_body):
                op = None
            else:
                op = g_script_body[e.pc]

            is_verify_target = (op is None
                                or op in (OP_VERIFY, OP_EQUALVERIFY,
                                          OP_NUMEQUALVERIFY)
                                # 'bugbyte' check
                                or (op == OP_CHECKMULTISIGVERIFY
                                    and e.cond.name == 'EQUAL'))
            if is_verify_target:
                verify_targets.append(e)

    txvalues = ctx.tx.values()
    got_model_values = (env.produce_model_values and
                        (ctx.used_witnesses or txvalues or ctx.stack
                         or g_data_placeholders))

    if env.produce_model_values:

        z3_push_context()

        if env.log_progress and got_model_values:
            print_as_header('Checking for non-variable model values',
                            level=2, is_solving=True)

        for wit in ctx.used_witnesses:
            wit.check_only_one_value_possible()

        processed = ctx.used_witnesses.copy()

        for txval in txvalues:
            assert txval not in processed, \
                ("only witnesses are processed at this point, tx values"
                    "cannot intersect")
            txval.check_only_one_value_possible()
            processed.append(txval)

        for val in g_data_placeholders.values():
            if val in processed:
                env.write_line(f'skip checking {val}: already checked')
            else:
                val.check_only_one_value_possible()
                processed.append(val)

        for i, val in enumerate(reversed(ctx.stack)):
            pos = -(i+1)
            if top and pos == -1:
                valname = '<result>'
            else:
                valname = f'stack[{pos}]'

            if val in processed:
                env.write_line(f'skip checking {valname}: already checked')
            else:
                val.check_only_one_value_possible(name=valname)
                processed.append(val)

        z3_pop_context()

    if env.check_always_true_enforcements and verify_targets:
        if env.log_progress:
            print_as_header('Checking for always-true enforcements',
                            level=2, is_solving=True)

        z3_push_context()

        for e in verify_targets:
            global g_skip_assertion_for_enforcement_condition
            g_skip_assertion_for_enforcement_condition = (e.cond, e.pc)

            ename = f'{e.cond} @ {op_pos_info(e.pc)}'
            if not is_cond_possible(use_as_script_bool(e.cond) == 0,
                                    e.cond, name=ename,
                                    fail_msg='  - always true'):
                e.is_always_true_in_path = True

            g_skip_assertion_for_enforcement_condition = None

        z3_pop_context()


def data_reference_names_show() -> None:

    g_seen_named_values.clear()

    seen_data_reference_names: set[str] = set()

    def get_data_reference_names_rec() -> list[tuple[list[str], str]]:
        result: list[tuple[list[str], str]] = []
        drn_copy = g_data_reference_names_table.copy()

        for _, vndict in drn_copy.items():
            data_reference_names: list[str] = []
            for dr, (value, ctx) in vndict.items():
                if dr not in seen_data_reference_names:
                    data_reference_names.append(dr)

                g_seen_named_values.add(value.unique_name)

            g_data_reference_names_table.clear()

            if data_reference_names:
                with CurrentExecContext(ctx):
                    result.append((data_reference_names, repr(value)))
                    seen_data_reference_names.update(data_reference_names)

            result.extend(get_data_reference_names_rec())

        g_seen_named_values.clear()
        g_data_reference_names_table.clear()

        return result

    for data_reference_names, val in get_data_reference_names_rec():
        cur_env().write_line(f'\t{" = ".join(data_reference_names)} = {val}')


def print_as_header(lines_or_str: str | Iterable[str], level: int = 0,
                    is_solving: bool = False, no_empty_line_above: bool = False
                    ) -> None:
    if level > 2:
        raise ValueError('unsupported header level')

    lines: Iterable[str]
    if isinstance(lines_or_str, str):
        lines = lines_or_str.split('\n')
    else:
        lines = lines_or_str

    chtop, chbottom = {0: ('=', '='), 1: (None, '-'), 2: (None, '~')}[level]

    env = cur_env()

    if not no_empty_line_above:
        env.ensure_empty_line()

    max_ll = max(len(ln) for ln in lines) if lines else 0
    if chtop:
        env.write_line(chtop*max_ll)
    env.write_line('\n'.join(lines))
    if chbottom:
        env.write_line(chbottom*max_ll)

    env = cur_env()

    if is_solving and env.log_solving_attempts_to_stderr:
        if not no_empty_line_above:
            env.solving_log_ensure_empty_line()
        if chtop:
            env.solving_log_line(chtop*max_ll)
        env.solving_log_line('\n'.join(lines))
        if chbottom:
            env.solving_log_line(chbottom*max_ll)


def report() -> None:  # noqa

    env = cur_env()

    enforcements_by_path: dict[tuple['Branchpoint', ...],
                               set['Enforcement']] = {}

    model_values_map: dict[tuple[str, ...],
                           tuple[int, list['ExecContext']]] = {}

    nonmodel_stack: list[SymData]

    unused_value_dict: dict[str, tuple['SymData', 'ExecContext']] = {}

    root_bp = env.get_root_branch()

    if not root_bp.context or not root_bp.context.failure:
        root_bp.process_always_true_enforcements()
        root_bp.process_unique_enforcements()
        unused_value_dict = root_bp.process_unused_values()

    if env.log_solving_attempts:
        env.solving_log_ensure_empty_line()

    got_warnings = False
    got_failures = False
    got_successes = False

    def model_value_line(sd: SymData) -> str:
        mr = sd.model_repr()

        if sd.is_only_one_value_possible:
            assert mr
            return f'= {mr}'

        return f': {mr or "?"}'

    def process_enf_paths(bp: Branchpoint, level: int) -> None:
        nonlocal got_successes
        nonlocal got_warnings
        nonlocal got_failures

        if bp.context:
            if bp.context.failure:
                got_failures = True
                return

            assert bp.context.is_finalized
            got_successes = True
            got_warnings |= bool(bp.context.warnings)
            mvals_list = []

            if env.produce_model_values:
                def get_val_str(v: SymData) -> str:
                    return model_value_line(v)

                txvalues = bp.context.tx.values()
                for txval in txvalues:
                    mvals_list.append(f'{txval} {get_val_str(txval)}')

                for vname, val in g_data_placeholders.items():
                    mvals_list.append(f'{vname} {get_val_str(val)}')

                for w in bp.context.used_witnesses:
                    mvals_list.append(f'{w} {get_val_str(w)}')
            else:
                def get_val_str(v: SymData) -> str:
                    return ': ?'

            stack_len = len(bp.context.stack)
            if not env.cleanstack_flag and stack_len > 0:
                for i, val in enumerate(reversed(bp.context.stack)):
                    pos = -(i+1)
                    vname = '' if not val._name else f'= {val} '
                    mvals_list.append(f'stack[{pos}] {vname}'
                                      f'{get_val_str(val)}')
            elif stack_len:
                assert stack_len == 1, \
                    "context should have failure set otherwise"
                top = bp.context.stack[-1]
                if mvals_list:
                    mvals_list.append('')

                vname = '' if not top._name else f'= {top} '
                mvals_list.append(f'<result> {vname}{get_val_str(top)}')
            else:
                assert stack_len == 0
                assert env.is_incomplete_script, \
                    "context should have failure set otherwise"

            mvals = tuple(mvals_list)

            num_witnesses = len(bp.context.used_witnesses)

            if mvals not in model_values_map:
                model_values_map[mvals] = (num_witnesses, [bp.context])
            else:
                model_values_map[mvals][1].append(bp.context)

        for e in bp.unique_enforcements or ():
            path = bp.get_enforcement_path(e)
            if path not in enforcements_by_path:
                enforcements_by_path[path] = set()
            enforcements_by_path[path].add(e)

    root_bp.walk_branches(process_enf_paths)

    paths = list(enforcements_by_path.keys())
    paths.sort(key=lambda p: tuple(bp.pc for bp in p))

    valid_paths: list[tuple['Branchpoint', ...]] = []

    def collect_valid_paths(bp: Branchpoint, level: int) -> None:
        if bp.context and not bp.context.failure:
            valid_paths.append(bp.get_path())

    if got_successes:
        root_bp.walk_branches(collect_valid_paths)

    if valid_paths:
        print_as_header('Valid paths:')

    with VarnamesDisplay(show_assignments=True):
        for path in valid_paths:
            print_as_header([bp.repr_for_path() for bp in path] or "[Root]",
                            level=1)

    if valid_paths:
        if paths:
            print_as_header('Enforced constraints per path:')
        else:
            print_as_header('No enforced constraints')

    with VarnamesDisplay(show_assignments=True):
        for path in paths:
            if path:
                print_as_header([bp.repr_for_path() for bp in path], level=1)
            else:
                print_as_header("All valid paths:", level=1)

            enflist = list(enforcements_by_path[path])
            enflist.sort(key=lambda bp: bp.pc)

            env.ensure_empty_line()

            for e in enflist:
                env.write_line(f'        {repr(e)}')

    env.ensure_empty_line()

    if unused_value_dict:
        print_as_header('Unused values:')
        with VarnamesDisplay(show_assignments=True):
            uvset: set[tuple[str, int]] = set()
            for uv, ctx in unused_value_dict.values():
                with CurrentExecContext(ctx):
                    uvset.add((f'{uv}', uv.src_pc))

            env.ensure_empty_line()

            combined_uvs = list(uvset)
            combined_uvs.sort(key=lambda v: v[1])
            for uvstr, src_pc in combined_uvs:
                env.write_line(f'\t{uvstr} from {op_pos_info(src_pc)}')

    if model_values_map:
        path_msg = 'per path' if len(model_values_map) > 1 else 'for all valid paths'
        if env.produce_model_values:
            print_as_header(f'Witness usage and model values {path_msg}:')
        elif env.is_incomplete_script:
            print_as_header(f'Witness usage and stack contents {path_msg}:')
        else:
            print_as_header(f'Witness usage {path_msg}:')

        for mvals, (num_witnesses, ctx_list) in model_values_map.items():
            assert len(ctx_list) > 0
            if len(model_values_map) > 1:
                with VarnamesDisplay():
                    for ctx in ctx_list:
                        print_as_header('\n'.join(ctx.get_timeline_strings()),
                                        level=1)

            env.write_line(f"Witnesses used: {num_witnesses}")
            env.ensure_empty_line()

            if env.produce_model_values or env.is_incomplete_script:
                if not env.produce_model_values:
                    env.write_line('Stack values:')
                else:
                    env.write_line('Model values:')
                for ws in mvals:
                    env.write_line(f'\t{ws}')

    env.ensure_empty_line()

    if got_warnings:
        print_as_header('Warnings per path:')

        def report_warnings(ctx: ExecContext) -> None:
            if ctx.warnings:
                with VarnamesDisplay():
                    print_as_header(
                        ctx.get_timeline_strings() or "All valid paths",
                        level=1)

                # In 'All valid path' case we could get duplicate
                # warnings, so we need to de-dup
                shown_warnings: set[str] = set()
                for pc, w in ctx.warnings:
                    w_str = f'{w} @ {op_pos_info(pc)}'
                    if w_str not in shown_warnings:
                        env.write_line(f'\t{w_str}')
                        shown_warnings.add(w_str)

                env.ensure_empty_line()

        root_bp.walk_contexts(report_warnings)

    env.ensure_empty_line()

    if got_failures:
        print_as_header('Failures per path:')

        def report_failures(ctx: ExecContext) -> None:
            if ctx.failure:
                with VarnamesDisplay(show_assignments=True):
                    print_as_header(
                        (ctx.get_timeline_strings(skip_failed_branches=False)
                         or "All paths"), level=1)

                finfo = ctx.failure_info
                if isinstance(finfo, str):
                    env.write_line(finfo)
                    env.ensure_empty_line()
                else:
                    pc = finfo[0]
                    env.write_line(f"Detected at {op_pos_repr(pc)} @ {op_pos_info(pc)}")
                    env.ensure_empty_line()
                    if len(finfo[1]) > 1:
                        print_as_header('One of:', level=2)
                    for info in finfo[1]:
                        env.write_line(info)
                        env.ensure_empty_line()

                if ctx.enforcements:
                    print_as_header("Enforcements before failure was detected:",
                                    level=2)

                    with VarnamesDisplay(show_assignments=True):
                        for e in ctx.enforcements:
                            env.write_line(f'\t{repr(e)}')

                    env.ensure_empty_line()

        root_bp.walk_contexts(report_failures, include_failed=True)

    points_of_interest = cur_env().points_of_interest
    if points_of_interest:
        print_as_header('Points of interest:')

        pc_list = []
        for poi in points_of_interest:
            if isinstance(poi, int):
                pc_list.append(poi)
            else:
                assert poi.startswith('L')
                line_no = int(poi[1:])
                for pc, lno in enumerate(g_line_no_table):
                    if line_no == lno:
                        pc_list.append(pc)
                        break
                else:
                    print_as_header(
                        f'Line {line_no} does not contain any operation',
                        level=1)

        def report_poi(ctx: ExecContext) -> None:
            global g_script_body

            print_as_header(
                (ctx.get_timeline_strings(skip_failed_branches=False)
                 or "All paths"), level=1)

            for pc in sorted(pc_list):
                if pc in ctx.exec_state_log:
                    if pc < len(g_script_body):
                        op_str = f' ({g_script_body[pc]})'
                    else:
                        op_str = ''

                    env.write_line(f"POI @ {op_pos_info(pc)}{op_str}:")
                    env.write_line(f"{ctx.exec_state_log[pc]}")
                    env.write_line("----")

            env.ensure_empty_line()

        root_bp.walk_contexts(report_poi, include_failed=True)


T_CSHA256 = TypeVar('T_CSHA256', bound='CSHA256')


class CSHA256():
    """
    This class provides access to SHA256 routines, with access to
    SHA256 midstate (which is not available from hashlib.sha256)

    The code is not constant-time! This should NOT be used for working with
    secret data, such as, for example  building a MAC (message authentication
    code), etc.

    The code in this class was manually ported by Dmitry Petukhov from
    C++ code in Bitcoin Core, by looking at C++ code and writing equivalent
    python code.

    Original C++ code was Copyright (c) 2014-2017 The Bitcoin Core developers
    Original C++ code was licensed under MIT software license.

    The code in this class is licensed under the same license as the whole
    file it is contained within is licensed under.

    As MIT license allows sublicensing, shall the code in this class be deemed
    a derivative work, it shall follow that the code in this class is
    re-licensed under the the same license as the whole file it is contained
    within is licensed under (see the header of the file, or accompanying
    LICENSE.md file)

    The following is the text of the license that comes with Bitcoin Core,
    and is included here solely for informational reference:

    The MIT License (MIT)

    Copyright (c) 2009-2021 The Bitcoin Core developers
    Copyright (c) 2009-2021 Bitcoin Developers

    Permission is hereby granted, free of charge, to any person obtaining a copy
    of this software and associated documentation files (the "Software"), to deal
    in the Software without restriction, including without limitation the rights
    to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
    copies of the Software, and to permit persons to whom the Software is
    furnished to do so, subject to the following conditions:

    The above copyright notice and this permission notice shall be included in
    all copies or substantial portions of the Software.

    THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
    IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
    FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
    AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
    LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
    OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN
    THE SOFTWARE.
    """

    __slots__ = ['s', 'buf', 'bytes_count']

    buf: bytes
    bytes_count: int
    s: list[int]

    # Initialize SHA-256 state.
    def __init__(self) -> None:
        self.Reset()

    # Perform a number of SHA-256 transformations, processing 64-byte chunks.
    def Transform(self, chunk: Union[bytes, bytearray], blocks: int) -> None:  # noqa
        if not isinstance(blocks, int):
            raise TypeError('blocks must be an instance of int')
        if not isinstance(chunk, (bytes, bytearray)):
            raise TypeError('chunk must be an instance of bytes or bytearray')

        def uint32(x: int) -> int:
            return x & 0xFFFFFFFF

        def sigma0(x: int) -> int:
            return (x >> 7 | x << 25) ^ (x >> 18 | x << 14) ^ (x >> 3)

        def sigma1(x: int) -> int:
            return (x >> 17 | x << 15) ^ (x >> 19 | x << 13) ^ (x >> 10)

        def ReadBE32(buf: bytes) -> int:
            return int(struct.unpack(b">I", buf[:4])[0])

        def Round(a: int, b: int, c: int, d: int, e: int, f: int, g: int, h: int,
                  k: int, w: int, x: list[int]) -> None:

            def uint32(x: int) -> int:
                return x & 0xFFFFFFFF

            def Maj(x: int, y: int, z: int) -> int:
                return (x & y) | (z & (x | y))

            def Ch(x: int, y: int, z: int) -> int:
                return z ^ (x & (y ^ z))

            def Sigma1(x: int) -> int:
                return (x >> 6 | x << 26) ^ (x >> 11 | x << 21) ^ (x >> 25 | x << 7)

            def Sigma0(x: int) -> int:
                return (x >> 2 | x << 30) ^ (x >> 13 | x << 19) ^ (x >> 22 | x << 10)

            t1 = uint32(x[h] + Sigma1(x[e]) + Ch(x[e], x[f], x[g]) + k + w)
            t2 = uint32(Sigma0(x[a]) + Maj(x[a], x[b], x[c]))
            x[d] = uint32(x[d] + t1)
            x[h] = uint32(t1 + t2)

        s = self.s
        while blocks:
            blocks -= 1
            a, b, c, d, e, f, g, h = range(8)
            x = s.copy()

            w0 = ReadBE32(chunk[0:])
            Round(a, b, c, d, e, f, g, h, 0x428a2f98, w0, x)
            w1 = ReadBE32(chunk[4:])
            Round(h, a, b, c, d, e, f, g, 0x71374491, w1, x)
            w2 = ReadBE32(chunk[8:])
            Round(g, h, a, b, c, d, e, f, 0xb5c0fbcf, w2, x)
            w3 = ReadBE32(chunk[12:])
            Round(f, g, h, a, b, c, d, e, 0xe9b5dba5, w3, x)
            w4 = ReadBE32(chunk[16:])
            Round(e, f, g, h, a, b, c, d, 0x3956c25b, w4, x)
            w5 = ReadBE32(chunk[20:])
            Round(d, e, f, g, h, a, b, c, 0x59f111f1, w5, x)
            w6 = ReadBE32(chunk[24:])
            Round(c, d, e, f, g, h, a, b, 0x923f82a4, w6, x)
            w7 = ReadBE32(chunk[28:])
            Round(b, c, d, e, f, g, h, a, 0xab1c5ed5, w7, x)
            w8 = ReadBE32(chunk[32:])
            Round(a, b, c, d, e, f, g, h, 0xd807aa98, w8, x)
            w9 = ReadBE32(chunk[36:])
            Round(h, a, b, c, d, e, f, g, 0x12835b01, w9, x)
            w10 = ReadBE32(chunk[40:])
            Round(g, h, a, b, c, d, e, f, 0x243185be, w10, x)
            w11 = ReadBE32(chunk[44:])
            Round(f, g, h, a, b, c, d, e, 0x550c7dc3, w11, x)
            w12 = ReadBE32(chunk[48:])
            Round(e, f, g, h, a, b, c, d, 0x72be5d74, w12, x)
            w13 = ReadBE32(chunk[52:])
            Round(d, e, f, g, h, a, b, c, 0x80deb1fe, w13, x)
            w14 = ReadBE32(chunk[56:])
            Round(c, d, e, f, g, h, a, b, 0x9bdc06a7, w14, x)
            w15 = ReadBE32(chunk[60:])
            Round(b, c, d, e, f, g, h, a, 0xc19bf174, w15, x)

            w0 = uint32(w0 + sigma1(w14) + w9 + sigma0(w1))
            Round(a, b, c, d, e, f, g, h, 0xe49b69c1, w0, x)
            w1 = uint32(w1 + sigma1(w15) + w10 + sigma0(w2))
            Round(h, a, b, c, d, e, f, g, 0xefbe4786, w1, x)
            w2 = uint32(w2 + sigma1(w0) + w11 + sigma0(w3))
            Round(g, h, a, b, c, d, e, f, 0x0fc19dc6, w2, x)
            w3 = uint32(w3 + sigma1(w1) + w12 + sigma0(w4))
            Round(f, g, h, a, b, c, d, e, 0x240ca1cc, w3, x)
            w4 = uint32(w4 + sigma1(w2) + w13 + sigma0(w5))
            Round(e, f, g, h, a, b, c, d, 0x2de92c6f, w4, x)
            w5 = uint32(w5 + sigma1(w3) + w14 + sigma0(w6))
            Round(d, e, f, g, h, a, b, c, 0x4a7484aa, w5, x)
            w6 = uint32(w6 + sigma1(w4) + w15 + sigma0(w7))
            Round(c, d, e, f, g, h, a, b, 0x5cb0a9dc, w6, x)
            w7 = uint32(w7 + sigma1(w5) + w0 + sigma0(w8))
            Round(b, c, d, e, f, g, h, a, 0x76f988da, w7, x)
            w8 = uint32(w8 + sigma1(w6) + w1 + sigma0(w9))
            Round(a, b, c, d, e, f, g, h, 0x983e5152, w8, x)
            w9 = uint32(w9 + sigma1(w7) + w2 + sigma0(w10))
            Round(h, a, b, c, d, e, f, g, 0xa831c66d, w9, x)
            w10 = uint32(w10 + sigma1(w8) + w3 + sigma0(w11))
            Round(g, h, a, b, c, d, e, f, 0xb00327c8, w10, x)
            w11 = uint32(w11 + sigma1(w9) + w4 + sigma0(w12))
            Round(f, g, h, a, b, c, d, e, 0xbf597fc7, w11, x)
            w12 = uint32(w12 + sigma1(w10) + w5 + sigma0(w13))
            Round(e, f, g, h, a, b, c, d, 0xc6e00bf3, w12, x)
            w13 = uint32(w13 + sigma1(w11) + w6 + sigma0(w14))
            Round(d, e, f, g, h, a, b, c, 0xd5a79147, w13, x)
            w14 = uint32(w14 + sigma1(w12) + w7 + sigma0(w15))
            Round(c, d, e, f, g, h, a, b, 0x06ca6351, w14, x)
            w15 = uint32(w15 + sigma1(w13) + w8 + sigma0(w0))
            Round(b, c, d, e, f, g, h, a, 0x14292967, w15, x)

            w0 = uint32(w0 + sigma1(w14) + w9 + sigma0(w1))
            Round(a, b, c, d, e, f, g, h, 0x27b70a85, w0, x)
            w1 = uint32(w1 + sigma1(w15) + w10 + sigma0(w2))
            Round(h, a, b, c, d, e, f, g, 0x2e1b2138, w1, x)
            w2 = uint32(w2 + sigma1(w0) + w11 + sigma0(w3))
            Round(g, h, a, b, c, d, e, f, 0x4d2c6dfc, w2, x)
            w3 = uint32(w3 + sigma1(w1) + w12 + sigma0(w4))
            Round(f, g, h, a, b, c, d, e, 0x53380d13, w3, x)
            w4 = uint32(w4 + sigma1(w2) + w13 + sigma0(w5))
            Round(e, f, g, h, a, b, c, d, 0x650a7354, w4, x)
            w5 = uint32(w5 + sigma1(w3) + w14 + sigma0(w6))
            Round(d, e, f, g, h, a, b, c, 0x766a0abb, w5, x)
            w6 = uint32(w6 + sigma1(w4) + w15 + sigma0(w7))
            Round(c, d, e, f, g, h, a, b, 0x81c2c92e, w6, x)
            w7 = uint32(w7 + sigma1(w5) + w0 + sigma0(w8))
            Round(b, c, d, e, f, g, h, a, 0x92722c85, w7, x)
            w8 = uint32(w8 + sigma1(w6) + w1 + sigma0(w9))
            Round(a, b, c, d, e, f, g, h, 0xa2bfe8a1, w8, x)
            w9 = uint32(w9 + sigma1(w7) + w2 + sigma0(w10))
            Round(h, a, b, c, d, e, f, g, 0xa81a664b, w9, x)
            w10 = uint32(w10 + sigma1(w8) + w3 + sigma0(w11))
            Round(g, h, a, b, c, d, e, f, 0xc24b8b70, w10, x)
            w11 = uint32(w11 + sigma1(w9) + w4 + sigma0(w12))
            Round(f, g, h, a, b, c, d, e, 0xc76c51a3, w11, x)
            w12 = uint32(w12 + sigma1(w10) + w5 + sigma0(w13))
            Round(e, f, g, h, a, b, c, d, 0xd192e819, w12, x)
            w13 = uint32(w13 + sigma1(w11) + w6 + sigma0(w14))
            Round(d, e, f, g, h, a, b, c, 0xd6990624, w13, x)
            w14 = uint32(w14 + sigma1(w12) + w7 + sigma0(w15))
            Round(c, d, e, f, g, h, a, b, 0xf40e3585, w14, x)
            w15 = uint32(w15 + sigma1(w13) + w8 + sigma0(w0))
            Round(b, c, d, e, f, g, h, a, 0x106aa070, w15, x)

            w0 = uint32(w0 + sigma1(w14) + w9 + sigma0(w1))
            Round(a, b, c, d, e, f, g, h, 0x19a4c116, w0, x)
            w1 = uint32(w1 + sigma1(w15) + w10 + sigma0(w2))
            Round(h, a, b, c, d, e, f, g, 0x1e376c08, w1, x)
            w2 = uint32(w2 + sigma1(w0) + w11 + sigma0(w3))
            Round(g, h, a, b, c, d, e, f, 0x2748774c, w2, x)
            w3 = uint32(w3 + sigma1(w1) + w12 + sigma0(w4))
            Round(f, g, h, a, b, c, d, e, 0x34b0bcb5, w3, x)
            w4 = uint32(w4 + sigma1(w2) + w13 + sigma0(w5))
            Round(e, f, g, h, a, b, c, d, 0x391c0cb3, w4, x)
            w5 = uint32(w5 + sigma1(w3) + w14 + sigma0(w6))
            Round(d, e, f, g, h, a, b, c, 0x4ed8aa4a, w5, x)
            w6 = uint32(w6 + sigma1(w4) + w15 + sigma0(w7))
            Round(c, d, e, f, g, h, a, b, 0x5b9cca4f, w6, x)
            w7 = uint32(w7 + sigma1(w5) + w0 + sigma0(w8))
            Round(b, c, d, e, f, g, h, a, 0x682e6ff3, w7, x)
            w8 = uint32(w8 + sigma1(w6) + w1 + sigma0(w9))
            Round(a, b, c, d, e, f, g, h, 0x748f82ee, w8, x)
            w9 = uint32(w9 + sigma1(w7) + w2 + sigma0(w10))
            Round(h, a, b, c, d, e, f, g, 0x78a5636f, w9, x)
            w10 = uint32(w10 + sigma1(w8) + w3 + sigma0(w11))
            Round(g, h, a, b, c, d, e, f, 0x84c87814, w10, x)
            w11 = uint32(w11 + sigma1(w9) + w4 + sigma0(w12))
            Round(f, g, h, a, b, c, d, e, 0x8cc70208, w11, x)
            w12 = uint32(w12 + sigma1(w10) + w5 + sigma0(w13))
            Round(e, f, g, h, a, b, c, d, 0x90befffa, w12, x)
            w13 = uint32(w13 + sigma1(w11) + w6 + sigma0(w14))
            Round(d, e, f, g, h, a, b, c, 0xa4506ceb, w13, x)
            Round(c, d, e, f, g, h, a, b, 0xbef9a3f7, w14 + sigma1(w12) + w7 + sigma0(w15), x)
            Round(b, c, d, e, f, g, h, a, 0xc67178f2, w15 + sigma1(w13) + w8 + sigma0(w0), x)

            s[0] = uint32(s[0] + x[a])
            s[1] = uint32(s[1] + x[b])
            s[2] = uint32(s[2] + x[c])
            s[3] = uint32(s[3] + x[d])
            s[4] = uint32(s[4] + x[e])
            s[5] = uint32(s[5] + x[f])
            s[6] = uint32(s[6] + x[g])
            s[7] = uint32(s[7] + x[h])

            chunk = chunk[64:]

    def Write(self: T_CSHA256, data: Union[bytes, bytearray]) -> T_CSHA256:
        if not isinstance(data, (bytes, bytearray)):
            raise TypeError('data must be instance of bytes or bytearray')

        if self.bytes_count + len(data) > SHA256_MAX:
            raise ValueError('total bytes count beyond max allowed value')

        bufsize = self.bytes_count % 64
        assert len(self.buf) == bufsize
        if bufsize and bufsize + len(data) >= 64:
            # Fill the buffer, and process it.
            remainder_len = 64 - bufsize
            buf = self.buf + data[:remainder_len]
            data = data[remainder_len:]
            self.bytes_count += remainder_len
            self.Transform(buf, 1)
            self.buf = b''
            bufsize = 0

        if len(data) >= 64:
            blocks = len(data) // 64
            self.Transform(data, blocks)
            data = data[64 * blocks:]
            self.bytes_count += 64 * blocks

        if len(data) > 0:
            assert len(data) < 64
            # Fill the buffer with what remains.
            self.buf = self.buf + data
            self.bytes_count += len(data)

        return self

    def Finalize(self) -> bytes:
        pad = b'\x80'+b'\x00'*63
        sizedesc = struct.pack(b">q", self.bytes_count << 3)
        self.Write(pad[:1 + ((119 - (self.bytes_count % 64)) % 64)])
        self.Write(sizedesc)
        return self.Midstate()

    def Midstate(self) -> bytes:
        s = self.s

        def ToBE32(x: int) -> bytes:
            return struct.pack(b">I", x)

        hash_chunks = []
        hash_chunks.append(ToBE32(s[0]))
        hash_chunks.append(ToBE32(s[1]))
        hash_chunks.append(ToBE32(s[2]))
        hash_chunks.append(ToBE32(s[3]))
        hash_chunks.append(ToBE32(s[4]))
        hash_chunks.append(ToBE32(s[5]))
        hash_chunks.append(ToBE32(s[6]))
        hash_chunks.append(ToBE32(s[7]))

        return b''.join(hash_chunks)

    def Reset(self) -> 'CSHA256':
        self.buf = b''  # type: bytes
        self.bytes_count = 0  # type: int
        self.s = [0x6a09e667,
                  0xbb67ae85,
                  0x3c6ef372,
                  0xa54ff53a,
                  0x510e527f,
                  0x9b05688c,
                  0x1f83d9ab,
                  0x5be0cd19]
        return self


def ripemd160(data: bytes) -> bytes:
    """
    Pure Python RIPEMD160 implementation.

    The code is not constant-time! This should NOT be used for working with
    secret data, such as, for example  building a MAC (message authentication
    code), etc.

    The code in this function is Copyright (c) 2021 Pieter Wuille.

    It was distributed under MIT software license along with Bitcoin Core
    test framework.

    Type annotations was added by Dmitry petukhov, as well as some
    code rearrangement.

    As MIT license allows sublicensing, the code in this function is
    re-licensed under the the same license as the whole file it is contained
    within is licensed under (see the header of the file, or accompanying
    LICENSE.md file)

    The following is the text of the license that comes with Bitcoin Core,
    and is included here solely for informational reference:

    The MIT License (MIT)

    Copyright (c) 2009-2021 The Bitcoin Core developers
    Copyright (c) 2009-2021 Bitcoin Developers

    Permission is hereby granted, free of charge, to any person obtaining a copy
    of this software and associated documentation files (the "Software"), to deal
    in the Software without restriction, including without limitation the rights
    to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
    copies of the Software, and to permit persons to whom the Software is
    furnished to do so, subject to the following conditions:

    The above copyright notice and this permission notice shall be included in
    all copies or substantial portions of the Software.

    THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
    IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
    FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
    AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
    LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
    OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN
    THE SOFTWARE.

    """

    # Message schedule indexes for the left path.
    ML = [
        0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15,
        7, 4, 13, 1, 10, 6, 15, 3, 12, 0, 9, 5, 2, 14, 11, 8,
        3, 10, 14, 4, 9, 15, 8, 1, 2, 7, 0, 6, 13, 11, 5, 12,
        1, 9, 11, 10, 0, 8, 12, 4, 13, 3, 7, 15, 14, 5, 6, 2,
        4, 0, 5, 9, 7, 12, 2, 10, 14, 1, 3, 8, 11, 6, 15, 13
    ]

    # Message schedule indexes for the right path.
    MR = [
        5, 14, 7, 0, 9, 2, 11, 4, 13, 6, 15, 8, 1, 10, 3, 12,
        6, 11, 3, 7, 0, 13, 5, 10, 14, 15, 8, 12, 4, 9, 1, 2,
        15, 5, 1, 3, 7, 14, 6, 9, 11, 8, 12, 2, 10, 0, 4, 13,
        8, 6, 4, 1, 3, 11, 15, 0, 5, 12, 2, 13, 9, 7, 10, 14,
        12, 15, 10, 4, 1, 5, 8, 7, 6, 2, 13, 14, 0, 3, 9, 11
    ]

    # Rotation counts for the left path.
    RL = [
        11, 14, 15, 12, 5, 8, 7, 9, 11, 13, 14, 15, 6, 7, 9, 8,
        7, 6, 8, 13, 11, 9, 7, 15, 7, 12, 15, 9, 11, 7, 13, 12,
        11, 13, 6, 7, 14, 9, 13, 15, 14, 8, 13, 6, 5, 12, 7, 5,
        11, 12, 14, 15, 14, 15, 9, 8, 9, 14, 5, 6, 8, 6, 5, 12,
        9, 15, 5, 11, 6, 8, 13, 12, 5, 12, 13, 14, 11, 8, 5, 6
    ]

    # Rotation counts for the right path.
    RR = [
        8, 9, 9, 11, 13, 15, 15, 5, 7, 7, 8, 11, 14, 14, 12, 6,
        9, 13, 15, 7, 12, 8, 9, 11, 7, 7, 12, 7, 6, 15, 13, 11,
        9, 7, 15, 11, 8, 6, 6, 14, 12, 13, 5, 14, 13, 13, 7, 5,
        15, 5, 8, 11, 14, 14, 6, 14, 6, 9, 12, 9, 12, 5, 15, 8,
        8, 5, 12, 9, 12, 5, 14, 6, 8, 13, 6, 5, 15, 13, 11, 11
    ]

    # K constants for the left path.
    KL = [0, 0x5a827999, 0x6ed9eba1, 0x8f1bbcdc, 0xa953fd4e]

    # K constants for the right path.
    KR = [0x50a28be6, 0x5c4dd124, 0x6d703ef3, 0x7a6d76e9, 0]

    def fi(x: int, y: int, z: int, i: int) -> int:
        """The f1, f2, f3, f4, and f5 functions from the specification."""
        if i == 0:
            return x ^ y ^ z
        elif i == 1:
            return (x & y) | (~x & z)
        elif i == 2:
            return (x | ~y) ^ z
        elif i == 3:
            return (x & z) | (y & ~z)
        elif i == 4:
            return x ^ (y | ~z)
        else:
            assert False

    def rol(x: int, i: int) -> int:
        """Rotate the bottom 32 bits of x left by i bits."""
        return ((x << i) | ((x & 0xffffffff) >> (32 - i))) & 0xffffffff

    def compress(h0: int, h1: int, h2: int, h3: int, h4: int, block: bytes
                 ) -> tuple[int, int, int, int, int]:
        """Compress state (h0, h1, h2, h3, h4) with block."""
        # Left path variables.
        al, bl, cl, dl, el = h0, h1, h2, h3, h4
        # Right path variables.
        ar, br, cr, dr, er = h0, h1, h2, h3, h4
        # Message variables.
        x = [int.from_bytes(block[4*i:4*(i+1)], 'little') for i in range(16)]

        # Iterate over the 80 rounds of the compression.
        for j in range(80):
            rnd = j >> 4
            # Perform left side of the transformation.
            al = rol(al + fi(bl, cl, dl, rnd) + x[ML[j]] + KL[rnd], RL[j]) + el
            al, bl, cl, dl, el = el, al, bl, rol(cl, 10), dl
            # Perform right side of the transformation.
            ar = rol(ar + fi(br, cr, dr, 4 - rnd) + x[MR[j]] + KR[rnd], RR[j]) + er
            ar, br, cr, dr, er = er, ar, br, rol(cr, 10), dr

        # Compose old state, left transform, and right transform into new state.
        return h1 + cl + dr, h2 + dl + er, h3 + el + ar, h4 + al + br, h0 + bl + cr

    # Initialize state.
    state = (0x67452301, 0xefcdab89, 0x98badcfe, 0x10325476, 0xc3d2e1f0)
    # Process full 64-byte blocks in the input.
    for b in range(len(data) >> 6):
        state = compress(*state, data[64*b:64*(b+1)])
    # Construct final blocks (with padding and size).
    pad = b"\x80" + b"\x00" * ((119 - len(data)) & 63)
    fin = data[len(data) & ~63:] + pad + (8 * len(data)).to_bytes(8, 'little')
    # Process final blocks.
    for b in range(len(fin) >> 6):
        state = compress(*state, fin[64*b:64*(b+1)])
    # Produce output.
    return b"".join((h & 0xffffffff).to_bytes(4, 'little') for h in state)

def main() -> None:  # noqa

    global g_script_body
    global g_line_no_table
    global g_var_save_positions

    env = cur_env()
    if env.z3_enabled:
        maybe_randomize_z3_seeds()

        if env.use_parallel_solving and \
                multiprocessing.get_start_method() != 'fork':
            sys.stderr.write("Parallel solving is not available, because "
                             "the system cannot use 'fork' method to start "
                             "new processes")
            env.use_parallel_solving = False

    if env.input_file == '-':
        lines = sys.stdin.readlines()
    else:
        with open(env.input_file) as f:
            lines = f.readlines()

    g_script_body, g_line_no_table, g_var_save_positions = \
        get_opcodes(lines)

    if g_script_body:
        global g_is_in_processing

        g_is_in_processing = True
        symex_script()
        g_is_in_processing = False
        report()


def sigint_handler(signo: int, frame: Any) -> None:
    if not g_is_in_processing:
        sys.exit(-1)


def sigchld_handler(_signum: int, _frame: Any) -> None:
    try:
        os.wait()
    except OSError:
        pass


def try_import_optional_modules() -> None:
    env = cur_env()
    if env.z3_enabled:
        if not g_optional_modules_register['z3']:
            try:
                global z3
                import z3
            except ImportError as e:
                sys.stderr.write(f'ERROR: Failed to import z3: {e}\n')
                sys.exit(-1)

            g_optional_modules_register['z3'] = True

    global g_secp256k1_handle
    global g_secp256k1_context
    global g_secp256k1_has_xonly_pubkeys
    if not g_optional_modules_register['secp256k1']:
        path = ctypes.util.find_library('secp256k1')
        if path is not None:
            try:
                g_secp256k1_handle = ctypes.cdll.LoadLibrary(path)
                g_secp256k1_context = g_secp256k1_handle.secp256k1_context_create(
                    0x101)  # 0x101 means 'verify' context type

                if g_secp256k1_context is None:
                    g_secp256k1_handle = None
                    sys.stderr.write(
                        f'ERROR:, secp256k1 library was found at {path}: and '
                        f'loaded, but secp256k1_context_create() failed')
                else:
                    g_secp256k1_handle.secp256k1_ec_pubkey_parse.restype = ctypes.c_int
                    g_secp256k1_handle.secp256k1_ec_pubkey_parse.argtypes = [ctypes.c_void_p, ctypes.c_char_p, ctypes.c_char_p, ctypes.c_size_t]
                    if getattr(g_secp256k1_handle, 'secp256k1_xonly_pubkey_parse', None):
                        g_secp256k1_handle.secp256k1_xonly_pubkey_parse.restype = ctypes.c_int
                        g_secp256k1_handle.secp256k1_xonly_pubkey_parse.argtypes = [ctypes.c_void_p, ctypes.c_char_p, ctypes.c_char_p]
                        g_secp256k1_has_xonly_pubkeys = True
            except Exception as e:
                sys.stderr.write(
                    f'ERROR:, secp256k1 library was found at {path}: but loading '
                    f'it retured error {e}')
                sys.stderr.flush()

        g_optional_modules_register['secp256k1'] = True

    env.load_plugin_modules()


def usage() -> None:
    progname = os.path.basename(sys.argv[0])
    print()
    print("B'SST: Bitcoin-like Script Symbolic Tracer")
    print()
    print("Copyright (c) 2023 Dmitry Petukhov (https://github.com/dgpv)")
    print()
    print(
        "Symbolically executes the opcodes, checks constraints that opcodes impose on\n"
        "values they process, and shows the report with conditions that the script\n"
        "enforce, possible failures, etc.")
    print()
    print("IMPORTANT: This program can help uncover problems with the scripts it analyses,\n"
          "BUT it cannot guarantee that there are no problems, inconsistenses, bugs,\n"
          "vulnerabilities, et cetera in the analyzed script. This program itself or the\n"
          "underlying libraries can also contain bugs or other inconsistencies that could\n"
          "preclude detection of the problems with the analyzed script. For some type\n"
          "of problems, the analysis algorithm just cannot detect them at all.\n")
    print("This program should be used as an additional layer of defence in the struggle\n"
          "to detect defects and unexpected behavior in the scripts, much like other\n"
          "things like testing or code audit are used for this purpose, simply reducing\n"
          "the probability of defects being undetected. It can also be used as a tool to\n"
          "better understand the behavior of analyzed scripts.")
    print()
    print(f"Free for non-commercial use. Licensed under Prosperity Public License 3.0.0.\n"
          f"Please run \"{progname} --license\" to display the license.\n")
    print(f"Contains portions of the code that was originally released under MIT software\n"
          f"license. These are code of the CSHA256 class (derived from MIT-licensed code,\n"
          f"that was authored by various Bitcoin Core developers) and ripemd160 function\n"
          f"(MIT-licensed code, authored by Pieter Wuille). Please refer to the source code\n"
          f"in {progname} for more information on these.")
    print()
    print("To be able to use Z3 for better analysis, \"z3-solver\" python package\n"
          "(https://pypi.org/project/z3-solver/) is needed")
    print()
    print("For the analyzer to check validity of statically-known public keys,\n"
          "secp256k1 library (https://github.com/bitcoin-core/secp256k1/) is needed")
    print()
    print(f"Usage: {progname} [options] [settings]")
    print()
    print("Available options:")
    print()
    print("  --help")
    print()
    print("        Show help on usage")
    print()
    print("  --license")
    print()
    print("        Show the software license this program is released under")
    print()
    print("  --version")
    print()
    print("        Show version")
    print()
    print("Available settings:")
    print()
    print("  Default value for each setting is shown after the '=' sign")
    print()

    dfl_env = SymEnvironment(is_for_usage_message=True)
    for key, value in SymEnvironment.__dict__.items():
        if SymEnvironment.is_option(key):
            name = key.replace('_', '-')
            text = re.sub('`(\\w+)`',
                          lambda m: '`--' + m.group(1).replace('_', '-') + '`',
                          value.__doc__)
            text = re.sub('^\\ *', '        ', text, flags=re.M)

            def transformed_value() -> str:
                dfl_v = getattr(dfl_env, key)
                if isinstance(dfl_v, bool):
                    return 'true' if dfl_v else 'false'
                elif isinstance(dfl_v, set):
                    return f"'{','.join(dfl_v)}'"
                elif isinstance(dfl_v, tuple):
                    return f"'{' '.join(str(elt) for elt in dfl_v)}'"
                elif isinstance(dfl_v, (int, float)):
                    return f"{dfl_v}"
                elif isinstance(dfl_v, SigVersion):
                    return dfl_v.name.lower()
                else:
                    return f"'{dfl_v}'"

            print(f'  --{name}={transformed_value()}\n\n{text}')


def show_license() -> None:
    print(sys.modules['bsst'].__doc__)

def parse_cmdline_args() -> None:  # noqa
    env = cur_env()

    for arg in sys.argv[1:]:
        if not arg.startswith('--'):
            sys.stderr.write("options should start with \"--\"\n")
            sys.exit(-1)

        if arg == '--help':
            usage()
            sys.exit()

        if arg == '--license':
            show_license()
            sys.exit()

        if arg == '--version':
            print(VERSION)
            sys.exit()

        if '=' in arg:
            argname, value_str = arg[2:].split('=')
        else:
            argname = arg[2:]
            value_str = ''

        name = argname.replace('-', '_')
        if not name.isidentifier():
            sys.stderr.write("Incorrect setting name\n")
            sys.exit(-1)

        if not SymEnvironment.is_option(name):
            sys.stderr.write(f"Unrecognized setting \"--{argname}\"\n")
            sys.exit(-1)

        if not value_str:
            sys.stderr.write(f"Value for \"--{argname}\" must be specified\n")
            sys.exit(-1)

        cur_v = getattr(env, name)
        if isinstance(cur_v, bool):
            if value_str == 'true':
                setattr(env, name, True)
            elif value_str == 'false':
                setattr(env, name, False)
            else:
                sys.stderr.write(
                    f"Setting \"--{argname}\" can be only 'true' or 'false'\n")
                sys.exit(-1)
        elif isinstance(cur_v, set):
            try:
                setattr(env, name, value_str.split(','))
            except ValueError as e:
                sys.stderr.write(f"Incorrect value for --{argname}: {e}'\n")
                sys.exit(-1)
        elif isinstance(cur_v, tuple):
            try:
                setattr(env, name, value_str.split())
            except ValueError as e:
                sys.stderr.write(f"Incorrect value for --{argname}: {e}'\n")
                sys.exit(-1)
        elif isinstance(cur_v, int):
            if not value_str.isdigit():
                sys.stderr.write(
                    f"Non-negative integer expected for --{argname}\n")
                sys.exit(-1)

            setattr(env, name, int(value_str))
        elif isinstance(cur_v, float):
            try:
                setattr(env, name, float(value_str))
            except ValueError as e:
                sys.stderr.write(f"Incorrect value for --{argname}: {e}'\n")
                sys.exit(-1)
        elif isinstance(cur_v, SigVersion):
            setattr(env, name, value_str)
        elif isinstance(cur_v, str):
            setattr(env, name, value_str)
        else:
            raise AssertionError('unhandled type of option value')


def main_cli() -> None:
    # multiprocessing.Pool might somtimes produce zombies, see
    # https://github.com/python/cpython/issues/88887
    # so we need a workaround, reap them ourselves
    pid = os.fork()
    if pid == 0:
        signal.signal(signal.SIGINT, sigint_handler)

        with CurrentEnvironment(SymEnvironment()):
            parse_cmdline_args()
            try_import_optional_modules()
            main()
    else:
        signal.signal(signal.SIGCHLD, sigchld_handler)
        signal.signal(signal.SIGINT, signal.SIG_IGN)
        try:
            os.waitpid(pid, 0)
        except OSError:
            pass


VERSION = "0.1.2.dev0"

if __name__ == '__main__':
    main_cli()
