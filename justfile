setup:
    #!/usr/bin/env bash
    echo "Setting up virtual enviroment"
    if command -v uv &> /dev/null; then
        uv sync
    else
        [ -d ".venv" ] || python3 -m venv .venv
        ./.venv/bin/python3 -m pip install -r requirements.txt
    fi
    echo "Virtual enviroment set up"

setup-test:
    #!/usr/bin/env bash
    if [ ! -d .venv ]; then
        just setup
    fi
    TEST_BIN_DIR="tests/binaries"
    [ -d $TEST_BIN_DIR ] || rm -rf $TEST_BIN_DIR
    echo "Setting up tests"
    ./scripts/install_solvers.sh tests/binaries --old-releases
    ./scripts/install_solvers.sh tests/binaries
    rm -f env.sh
    .venv/bin/python -m pysmt install --z3 --confirm-agreement
    echo "Tests setup"
    echo CVC5_1_0_5_HOME=./$TEST_BIN_DIR/cvc5-1.0.5/bin > .env.test
    echo ELDARICA_2_0_9_HOME=./$TEST_BIN_DIR/eldarica-2.0.9 >> .env.test
    echo GOLEM_0_4_0_HOME=./$TEST_BIN_DIR/golem-0.4.0 >> .env.test
    echo OPENSMT_2_5_0_HOME=./$TEST_BIN_DIR/opensmt-2.5.0 >> .env.test

    echo CVC5_HOME=./$TEST_BIN_DIR/cvc5-1.3.2/bin >> .env.test
    echo ELDARICA_HOME=./$TEST_BIN_DIR/eldarica-2.2.1 >> .env.test
    echo GOLEM_HOME=./$TEST_BIN_DIR/golem-50f3b1a/build >> .env.test
    echo OPENSMT_HOME=./$TEST_BIN_DIR/opensmt-2.9.2 >> .env.test
    echo Z3_HOME=./$TEST_BIN_DIR/z3-4.15.4-x64-glibc-2.39/bin >> .env.test

test:
    ./.venv/bin/pytest
    rm -f tmp.smt2 > /dev/null

clean:
    rm -rf .venv
    rm -rf tests/binaries
    rm -rf .pytest_cache
    rm -f .env.test
    find . -type f -name "__pycache__" -delete
