#!/bin/sh

set -ex

./test_integer_conversion.py
./test_varnames.py
./test_elements_script_tests.py ./script_tests_tapscript_opcodes.json
if [ ! -e script_tests.json ]; then
    wget https://raw.githubusercontent.com/ElementsProject/elements/master/src/test/data/script_tests.json
fi
./test_elements_script_tests.py ./script_tests.json
./test_scripts.py
