# pyCHC: A library for certified CHC solving

## Installation

Install `pySMT` module
```
pip install -r requirements.txt
```

Install some SMT solvers from `pySMT`
```
python -m pysmt install --z3 --confirm-agreement
```

## Run toy example

```
python -m example.sat_check
```

## Run tests
```
python -m pytest pychc/tests
```


