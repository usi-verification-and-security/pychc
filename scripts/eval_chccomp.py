import json

from pathlib import Path
from subprocess import TimeoutExpired
import time

from pysmt.logics import QF_UFLIA

from pychc.chc_system import CHCSystem
from pychc.exceptions import PyCHCInvalidResultException, PyCHCSolverException
from pychc.solvers.golem import GolemSolver
from pychc.solvers.z3 import Z3CHCSolver
from pychc.solvers.eldarica import EldaricaSolver
from pychc.solvers.cvc5 import CVC5Solver
from pychc.solvers.carcara import Carcara
from pychc.solvers.witness import ProofFormat, Status

from pychc.tests.common import reset_pysmt_env

import argparse

BENCHDIR = Path(__file__).parent.parent.parent / "chc-comp25-benchmarks"

def get_smt2(line: str) -> Path:
    yml = BENCHDIR / line.strip()
    with open(yml, "r") as f:
        for l in f:
            if l.startswith("input_files:"):
                smt2 = l.split(":", 1)[1].strip()
                return yml.parent / smt2
    assert False, "no Input file string in yaml"

def get_all_benchmarks(category : str) -> list[Path]:
    bench_set = BENCHDIR / category
    if not bench_set.exists():
        if not Path(category).exists():
            raise FileNotFoundError(f"Benchmark set {category} not found")
        bench_set = Path(category)
    with open(bench_set, "r") as f:
        return list(map(get_smt2, filter(lambda x : x.strip() and not x.strip().startswith("#"), map(str.strip, f.readlines()))))

def load_solved(json_path: Path) -> dict:
    import json
    if json_path.exists():
        print("Loading existed results from ", json_path.resolve())
        return json.load(open(json_path, "r"))
    else:
        print(f"File {json_path} not found. Starting with empty results.")
        return {}

def get_test_family(test: Path) -> str:
    while test.parent != BENCHDIR:
        test = test.parent
    return test.name

@reset_pysmt_env
def run_test(solver, test, TO):
    print(f"  Running {solver.get_name()}...", end='', flush=True)
    solving_time = TO + 1
    try:
        start = time.time()
        status = solver.run(test, timeout=TO)
        solving_time = round(time.time() - start, 2)
    except Exception as e:
        print(f"\n{solver.get_name()} failed on {test} with exception: {e}")
        return "error", None, solving_time

    # with CVC5Solver(proof_checker=Carcara()) as smt_validator:
    with CVC5Solver() as smt_validator:
        validated = None
        if status == Status.SAT:
            try:
                print(f"{status.value}. Validating model...", end='', flush=True)
                sys = CHCSystem.load_from_file(Path(test), logic=QF_UFLIA)
                sys.validate_sat_model(solver.get_witness(), smt_validator, timeout=2*TO)
                print("Valid!")
                validated = True
            except (PyCHCInvalidResultException, PyCHCSolverException) as e:
                print(f"Validation failed! {e}")
                validated = False
            except TimeoutExpired:
                print("Validation timeout")
        elif status == Status.UNSAT and solver.get_name() == "golem":
            try:
                print(f"{status.value}. Validating proof...", end='', flush=True)
                Carcara().validate_witness(solver.get_witness(), smt2file=test, timeout=TO)
                print("Valid!")
                validated = True
            except PyCHCInvalidResultException as e:
                validated = False
                print(f"Validation failed! {e}")
            except TimeoutExpired:
                print("Validation timeout")
        else:
            print(f'{status.value}')
    return str(status.value) if isinstance(status, Status) else str(status), validated, solving_time

def test_spacer(test: Path, TO):
    spacer = Z3CHCSolver(global_guidance=True)
    return run_test(spacer, test, TO)

def test_eldarica(test: Path, TO):
    eldarica = EldaricaSolver()
    return run_test(eldarica, test, TO)

def test_golem(test: Path, TO):
    golem = GolemSolver()
    golem.set_unsat_proof_format(ProofFormat.ALETHE)
    return run_test(golem, test, TO)

def get_key(path: Path) -> str:
    return str(path.relative_to(BENCHDIR))

def initialize_missing_entries(solved: dict, key: str):
    if key not in solved:
        solved[key] = {}
    for solver in ["z3", "eldarica", "golem"]:
        if solver not in solved[key]:
            solved[key][solver] = {"status": "unknown", "validated": None, "solving_time": None}

def main(args):
    BENCHMARKS = get_all_benchmarks(args.bench_set)    
    n = len(BENCHMARKS)
    print("Tot Benchmarks: ", n)

    if args.resume:
        SOLVED = load_solved(args.json)
    else:
        SOLVED = {}

    print('='*40)
    MAX_N = args.max_nr if args.max_nr is not None else n

    solvers = [args.solver] if args.solver != "all" else ["z3", "eldarica", "golem"]
    new = 0
    for i, test in enumerate(BENCHMARKS):

        to_check = (
            (args.max_nr is None or i < args.max_nr)
            and not (
                # if resume, run only if not already fully solved with the selected solvers
                args.resume
                and get_key(test) in SOLVED
                and set(solvers).issubset(set(SOLVED[get_key(test)]))
                )
        )
        if not to_check:
            continue

        print(f"[{i+1}/{MAX_N}] Testing {test}")

        new += 1
        initialize_missing_entries(SOLVED, get_key(test))

        if args.solver == "all" or args.solver == "z3":
            status, validated, solving_time = test_spacer(test, args.timeout)
            SOLVED[get_key(test)]["z3"] = {
                "status": status, "validated": validated, "solving_time": solving_time
            }
        if args.solver == "all" or args.solver == "eldarica":
            status, validated, solving_time = test_eldarica(test, args.timeout)
            SOLVED[get_key(test)]["eldarica"] = {
                "status": status, "validated": validated, "solving_time": solving_time
            }
        if args.solver == "all" or args.solver == "golem":
            status, validated, solving_time = test_golem(test, args.timeout)
            SOLVED[get_key(test)]["golem"] = {
                "status": status, "validated": validated, "solving_time": solving_time
            }

        # Periodically save results to avoid losing progress in case of interruption
        if new % 10 == 0:
            json.dump(SOLVED, open(args.json, "w"), indent=4)

    json.dump(SOLVED, open(args.json, "w"), indent=4)


    print("="*40)
    print("Results printed in: ", args.json.resolve())
    print("="*40)

    print(f"Analyzed benchmarks: {len(SOLVED)}")

    for solver in solvers:
        print(f"\nResults for {solver}:")
        solved = [v for v in SOLVED.values() if v[solver]['status'] != 'unknown']
        print(f"\tSolved benchmarks: {len(solved)}")
        sat = [v for v in SOLVED.values() if v[solver]['status'] == 'sat']
        print(f"\tSAT benchmarks: {len(sat)}")
        validated_sat = [v for v in sat if v[solver]['validated'] == True]
        print(f"\t -- validated: {len(validated_sat)}/{len(sat)}")
        unsat = [v for v in SOLVED.values() if v[solver]['status'] == 'unsat']
        print(f"\tUNSAT benchmarks: {len(unsat)}")
        validated_unsat = [v for v in unsat if v[solver]['validated'] == True]
        print(f"\t -- validated: {len(validated_unsat)}/{len(unsat)}")

def parse_args():
    parser = argparse.ArgumentParser()
    parser.add_argument("bench_set", type=str, help="Benchmark set (e.g., 'LIA.set', or 'LIA-Lin.set' or path to custom set file)")
    parser.add_argument("--solver", type=str, default="all", choices=["z3", "eldarica", "golem", "all"], help="Solver to run (default: all)")
    parser.add_argument("--json", type=Path, default=None, help="Path to json file to store results")
    parser.add_argument("--timeout", type=int, default=30, help="Timeout for solver in seconds")
    parser.add_argument("-N", "--max-nr", type=int, default=None, help="Maximum number of benchmarks to analyze")
    parser.add_argument("--resume", action="store_true", help="Whether to resume from existing .json. Any test already present in the json file are not re-run.")
    args = parser.parse_args()
    category_name = Path(args.bench_set).stem
    if args.json is None:
        args.json = Path(__file__).parent / f"{category_name}_result_{args.solver}.json"
    return args

if __name__ == "__main__":
    args = parse_args()
    main(args)
