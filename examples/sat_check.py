from pathlib import Path

from pychc.solvers.witness import SatWitness, Status
from pychc.chc_system import CHCSystem
from pychc.solvers import golem, eldarica, z3, opensmt, cvc5, carcara

from pysmt.typing import INT
from pysmt.logics import QF_UFLIA
from pysmt.shortcuts import And, Symbol, Int, Plus, FALSE, LT
from pychc.shortcuts import Predicate, Apply, Clause

import logging
logging.basicConfig(level=logging.CRITICAL)


if __name__ == "__main__":

    # Create a CHC system
    sys = CHCSystem(logic=QF_UFLIA)

    # Create a predicate inv(x: Int)
    inv = Predicate("inv", [INT])
    sys.add_predicate(inv)
    x = Symbol("x", INT)
    sys.add_clauses(    
        {
            # init clause: inv(0)
            Clause(head=Apply(inv, [Int(0)])),
            # transition clause: inv(x) & -> inv(x + 1)
            Clause(body=Apply(inv, [x]), head=Apply(inv, [Plus(x, Int(1))])),
            # goal clause: inv(x) & x < 0 -> FALSE
            Clause(body=And(Apply(inv, [x]), LT(x, Int(0))), head=FALSE()),
        }
    )
    print("Created CHC system:")
    for clause in sys.get_clauses():
        print(clause.serialize())

    # Create a Golem solver with OpenSMT as validator of SAT answers, and Carcara as validator of UNSAT proofs
    print("\nSolving with Golem. Validate SAT answers with OpenSMT and UNSAT proofs with Carcara....")
    solver = golem.GolemSolver(
        smt_validator=opensmt.OpenSMTSolver(logic=QF_UFLIA),
        proof_checker=carcara.Carcara()
    )
    # Assign the system to the solver
    solver.load_system(sys)
    status = solver.solve(validate=True)
    print(f"Golem returned status: {status}. Result was validated!")

    # Extract the Witness from the solver
    witness = solver.get_witness()

    # Print the witness definitions
    print("\nWitness found by Golem:")
    print(witness.serialize_to_string())

    print("*" * 20)

    ## We can validate an externally provided witness on an externally provided system.

    # Let's serialize the witness and system to files to simulate they are provided as external files.

    # Serialize the CHC system to a file
    sys_file = Path("chc_example2.smt2")
    print(f"\nSerializing CHC system to {sys_file}")
    sys.serialize(sys_file)

    # Serialize the witness to a file
    witness_file = Path("sat_witness.smt2")
    print(f"Serializing SAT witness to {witness_file}")
    witness.serialize(witness_file)

    print("*" * 20)

    # Now, let's validate "sat_witness.smt2" on "chc_example2.smt2"
    # We now use CVC5 as SMT validator, whose results can be internally checked with Carcara.
    print(f"\nLoad CHC system from {sys_file} and a witness from {witness_file}, and validate with CVC5 + Carcara....")
    read_system = CHCSystem.load_from_file(sys_file)
    read_witness = SatWitness.load_from_file(witness_file)
    smt_validator = cvc5.CVC5Solver(logic=QF_UFLIA, proof_checker=carcara.Carcara())
    read_system.validate_sat_model(read_witness, smt_validator)
    print("The witness is valid for the system according to CVC5 + Carcara!")

    print("*" * 20)

    ## We can also run a CHC solver directly on an smt2 file without loading it first.
    # This ensures to run syntactically the input provided.

    # This solver has not smt_validator / proof_checker, so no validation is done internally.
    print(f"\nRun Eldarica on {sys_file} without parsing it first....")
    solver2 = eldarica.EldaricaSolver()
    # no need to load the system, we can run directly on the file. If the file contains (check-sat), it stores a status.
    solver2.run(sys_file)
    status2 = solver2.get_status()
    assert status2 == Status.SAT
    print("Eldarica returned SAT on the input file")
    # We can inspect the witness found by the solver
    witness2 = solver2.get_witness()
    print("\nValidating the witness found by Eldarica with Z3....")
    CHCSystem.load_from_file(sys_file).validate_sat_model(witness2, z3.Z3SMTSolver())
    print("The witness is valid for the system!")

    print("\nWitness found by Eldarica:")
    print(witness2.serialize_to_string())

    assert status2 == Status.SAT and isinstance(witness2, SatWitness)
    print("\nAnother informal way to look at the witness:")
    for var, expr in witness2.definitions.items():
        print(f"{var} := {expr.function_body.serialize()}")

    # Clean up
    sys_file.unlink()
    witness_file.unlink()
