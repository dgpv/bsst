#!/bin/sh

set -ex

export IS_BSST_TESTS_IS_IN_PROGRESS=1

./test_size_reports.sh
./test_name_aliases.sh
./test_dynamic_stack_access.sh
./test_plugins.sh
./test_integer_conversion.py
./test_data_placeholders.py
./test_varnames.py
./test_assertions_and_assumptions.py
./test_hooks.py
./test_elements_script_tests.py ./script_tests_tapscript_opcodes.json tapscript
if [ ! -e script_tests.json ]; then
    wget https://raw.githubusercontent.com/ElementsProject/elements/master/src/test/data/script_tests.json
fi
./test_elements_script_tests.py ./script_tests.json
./test_scripts.py

echo "SUCCESS"
