# BoolCrypt 0.1

BoolCrypt is a Python 3 library for vectorial Boolean functions in cryptography. In particular, it provides the following features:

- Represent vectorial Boolean functions in ANF, LUT, univariate polynomials and matrices and change one representation to another.
- List of 3- 4- 5- and 6- bit affine classes and some classes of rotation-symmetric S-boxes.
- Classify a list of S-boxes according to some cryptographic properties.
- Find permutations, rotation-symmetric,reduced-size,... binary and non-binary polynomials.
- Find whether two functions are linear or affine equivalent and count the number of linear or affine self-equivalences.
- Solve functional equations and linear/affine/CCZ equivalence and self-equivalence problems using SAT solvers.

Most of the functions and classes in BoolCrypt contain many examples of their usage in their docstrings,
also available in the HTML documentation in [html_documentation.zip](html_documentation.zip).

BoolCrypt was proposed in [Implicit White-Box Implementations: White-Boxing ARX Ciphers](https://eprint.iacr.org/2022/XXX),
and it is a dependency of [whiteboxarx](https://github.com/ranea/whiteboxarx).

## Installation

BoolCrypt requires Python >= 3.7 and SageMath >= 9.1.
Although BoolCrypt is meant to be used as a Python library, it can also be used in a Sage shell.

Solving functional equations or equivalence problems requires CryptoMiniSat, which can be installed in SageMath by
```
sage -i cryptominisat
```

BoolCrypt also requires [sboxU](https://github.com/lpp-crypto/sboxU) v1.0., 
but with some modifications described in [modifications_sboxU.md](modifications_sboxU.md).
A modified version of sboxU is given in the directory [sboxU](sboxU).
Then compile the modified sboxU by
```
cd sboxU/sboxU_cython
sage setup.py build_ext --inplace
```
