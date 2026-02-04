from pathlib import Path

from pychc.exceptions import PyCHCInvalidResultException
from pychc.chc_system import CHCSystem
from pychc.solvers import z3, cvc5, golem

from pysmt.shortcuts import Symbol, is_valid, Iff

import logging

logging.basicConfig(level=logging.DEBUG)

this_dir = Path(__file__).parent
test_file = this_dir / "example.smt2"

# Investigate the CHC system in the example file
sys = CHCSystem.load_from_file(test_file)
print(
    f"Loaded CHC has: {len(sys.get_predicates())} predicates, {len(sys.get_clauses())} clauses"
)

print("*" * 20)
print("Running Spacer on the file...")
spacer = z3.Z3CHCSolver(global_guidance=True)
spacer.run(test_file)
spacer_witness = spacer.get_witness()
print("Validating witness with CVC5 solver...")
try:
    sys.validate_sat_model(spacer_witness, smt_validator=cvc5.CVC5Solver())
    print("Spacer's witness is valid!")
except PyCHCInvalidResultException as e:
    print(f"Validation of witness produced with Spacer failed: {e}")

print("*" * 20)
print("Running Golem solver on the same file...")
golem = golem.GolemSolver(engine=golem.GolemEngines.split_tpa)
golem.run(test_file)
witness_golem = golem.get_witness()
print("Validating Golem's witness with CVC5 solver...")
try:
    sys.validate_sat_model(witness_golem, smt_validator=cvc5.CVC5Solver())
    print("Golem's witness is valid!")
except PyCHCInvalidResultException as e:
    print(f"Validation of witness produced with Golem failed: {e}")

print("*" * 20)
print("Comparing the two witnesses...")
for predicate in sys.get_predicates():
    print("*" * 10)
    pname = predicate.symbol_name()
    golem_interp = witness_golem.definitions[pname]
    spacer_interp = spacer_witness.definitions[pname]

    # 0-arity predicates
    if not predicate.get_type().is_function_type():
        print(f"Predicate {predicate.symbol_name()}:", end=" ")
        if golem_interp != spacer_interp:
            print("Golem and Spacer interpretations differ!")
            print(f"Golem : {golem_interp}")
            print(f"Spacer: {spacer_interp}")
        else:
            print("Golem and Spacer interpretations match!")
            print(f"Both  : {golem_interp}")
        continue
    
    # n-arity predicates (n > 0)
    golem_vars, golem_body = golem_interp.formal_params, golem_interp.function_body
    spacer_vars, spacer_body = spacer_interp.formal_params, spacer_interp.function_body
    # Rename variables to a common set for comparison
    assert len(golem_vars) == len(spacer_vars)
    assert all(
        gv.symbol_type() == sv.symbol_type() for gv, sv in zip(golem_vars, spacer_vars)
    )
    new_vars = [
        Symbol(f"{pname}_v{i}", v.symbol_type()) for i, v in enumerate(golem_vars)
    ]
    golem_body = golem_interp.function_body.substitute(
        {v: new_v for v, new_v in zip(golem_vars, new_vars)}
    )
    spacer_body = spacer_interp.function_body.substitute(
        {v: new_v for v, new_v in zip(spacer_vars, new_vars)}
    )

    if not is_valid(Iff(golem_body, spacer_body)):
        print("Golem and Spacer interpretations differ!")
        print(f"Golem : {golem_body.serialize()}")
        print(f"Spacer: {spacer_body.serialize()}")
    else:
        print("Golem and Spacer interpretations match!")
        print(f"Both  : {golem_body.serialize()}")
