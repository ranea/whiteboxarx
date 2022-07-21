# Implicit White-box Implementations of ARX Ciphers

This repository contains Python scripts to generate implicit white-box implementations of ARX ciphers following the method described in the paper [Implicit White-Box Implementations: White-Boxing ARX Ciphers](https://eprint.iacr.org/2022/428).

Note that this repository is an early prototype and some details/features of the implicit framework are not fully implemented yet.

## Requirements

* Python 3 (version >= 3.7)
* [BoolCrypt](https://github.com/ranea/boolcrypt) (version >= 0.1.1)
* [SageMath](https://www.sagemath.org/) equipped with [CryptoMiniSat](https://github.com/msoos/cryptominisat)
* [gcc](https://gcc.gnu.org/) or another C compiler (to compile exported C code)
* [M4RI](https://bitbucket.org/malb/m4ri) (to compile exported C code)

## Usage (Linux)

### 1 - Setting the environment variables

First, append to the environment variable `PYTHONPATH` the directory containing the `boolcrypt` library and this repository

```
export PYTHONPATH=".../boolcrypt-master:.../whiteboxarx-master"
```

In a virtual environment, [add2virtualenv](https://virtualenvwrapper.readthedocs.io/en/latest/command_ref.html#add2virtualenv) can be used to add folders to the `PYTHONPATH`.

### 2 - Generating the affine layers

To generate the white-box implementation of a given ARX cipher, first we need to generate the (unencoded) affine layers of the encryption function of the given cipher (for a fixed key). 

The script `speck.py` implements this step for the cipher Speck, which can be invoked from the command line as follows

```
usage: sage -python speck.py [-h] [--key KEY [KEY ...]] [--block-size [{8,32,64,128}]] [--output-file [OUTPUT_FILE]]

Generate the implicit (unencoded) and explicit affine layers of a Speck instance for a fixed key

options:
  -h, --help            show this help message and exit
  --key KEY [KEY ...]   the master key given as a hexadecimal representation of the words
  --block-size [{8,32,64,128}]
                        the block size in bits of the Speck instance
  --output-file [OUTPUT_FILE]
                        the file to store the implicit (unencoded) and explicit affine layers
```

For example, to generate the unencoded affine layers of `Speck32/64` using the key `1918 1110 0908 0100` and to store these layers in the file `speck32_64_affine_layers.sobj`

```
$ sage -python speck.py --key 1918 1110 0908 0100 --block-size 32 --output-file speck32_64_affine_layers.sobj 
```

Note that the script `speck.py` and the other scripts can be either be invoked with `sage -python [...]` or with `sage -sh; python [...]`.

Currently, the generation of the unencoded affine layers is only implemented for some instances Speck, but other ARX cipher can be implemented by adapting `speck.py`.

### 3 - Generating the implicit round functions

The next step is to generate the implicit (encoded) round functions that form the implicit white-box implementation. This is done by `generate_wb.py`

```
usage: sage -python generate_wb.py [-h] [--input-file INPUT_FILE] [--irf-degree {2,3,4}] [--output-file OUTPUT_FILE] [--seed SEED] [--trivial-affine-encodings] [--trivial-quadratic-encodings] [--trivial-external-encodings]
                                   [--trivial-graph-automorphisms [{repeat}]] [--trivial-redundant-perturbations] [--disable-redundant-perturbations] [--disable-max-degree] [--print-time-generation] [--print-debug-generation]
                                   [--debug-file DEBUG_FILE]

Generate an implicit white-box implementation of a given ARX cipher

options:
  -h, --help            show this help message and exit
  --input-file INPUT_FILE
                        the file containing the implicit (unencoded) and explicit affine layers
  --irf-degree {2,3,4}  the degree of the implicit encoded round functions
  --output-file OUTPUT_FILE
                        the file to store the implicit encoded round functions and the external excodings
  --seed SEED           the seed used to generate random values (default: 0)
  --trivial-affine-encodings
                        use trivial affine encodings
  --trivial-quadratic-encodings
                        use trivial quadratic encodings
  --trivial-external-encodings
                        use trivial external encodings
  --trivial-graph-automorphisms [{repeat}]
                        use trivial graph automorphisms (if set to 'repeat', the same graph automorphism is used for each round)
  --trivial-redundant-perturbations
                        use trivial redundant perturbations
  --disable-redundant-perturbations
                        disable the countermeasure based on redundant perturbations
  --disable-max-degree  disable sampling encondings until all implicit encoded round functions have exactly irf-degree
  --print-time-generation
                        print time generation output
  --print-debug-generation
                        print debug information output
  --debug-file DEBUG_FILE
                        the file to store the debug output (default: stdout)
```

The main arguments of `generate_wb.py` are `--input-file`, `--irf-degree` and `--output-file`. The `input-file` parameter points to the file generated in the previous step (the unencoded affine layers of the cipher pickled using SageMath's `save` function), the `irf-degree` selects the degree of the implicit round functions, and `output-file` specifies the file to store the implicit round functions. Additional debugging information can be output using `print-time-generation` and `print-debug-generation`, and saved using `debug-file`.

Thus, to generate an implicit implementation of Speck32/64 for the previous key, using cubic implicit round functions

```
sage -python generate_wb.py --input-file speck32_64_affine_layers.sobj --irf-degree 3 --output-file speck32_64_irf.sobj
```

Note that `generate_wb.py` can take several hours due to the generation of the graph automorphisms and affine-quadratic self-equivalences.

There are some restrictions on some parameters:

- The parameter `trivial-quadratic-encodings` is only used when `irf-degree` is set to 3 or 4; if enabled, the round encodings only contain affine permutations and not affine-quadratic self-equivalences.
- The additional countermesaure based on redundant perturbations can be used with trivial perturbations with `trivial-redundant-perturbations` or can be totally disabled with `disable-redundant-perturbations`, but these two parameters cannot be combined.

Current limitations:

- `generate_wb.py` only supports ARX ciphers where the $n$-bit non-linear layer of each round is the permuted modular addition with wordisize $n/2$ (input bit-size $n$), and where $n$ is a power of 2. In other words, `generate_wb.py` assumes that between each pair of consecutive affine layers (given in the `input-file`) there is a single permuted modular addition with maximum wordisize, and that the first and last layer are affine layers.
- if `trivial-graph-automorphisms` is not given, the graph automorphisms are sampled not uniformly (due to the use of a SAT solver) and from a very small subset stored in `stored_cczse_pmodadd_w*.sobj` (that does not contain all graph automorphisms of the permuted modular addition).
- if `irf-degree` is 3 or 4 and `trivial-quadratic-encodings` is not given, the affine-quadratic self-equvialences are sampled not uniformly (due to the use of a SAT solver).
- if `irf-degree` is 2 and `trivial-external-encodings` is not given, the input and output external encodings are chosen as affine permutations.
- if `irf-degree` is 3 or 4 and `trivial-external-encodings` is not given, the input external encoding is chosen as an affine permutation, and the output external encoding is chosen such that its inverse is quadratic (built from an affine-quadratic self-equivalence of the permuted modular addition).

### 4 - Evaluating the implicit white-box implementation with Python

The white-box implementation (i.e., the implicit round functions) generated in the previous step can be evaluated for a given plaintext with the Python script `eval.py`.

```
usage: sage -python eval_wb.py [-h] [--input-file INPUT_FILE] [--plaintext PLAINTEXT PLAINTEXT] [--cancel-external-encodings] [--disabled-redundant-perturbations] [--output-file OUTPUT_FILE] [--print-intermediate-values]
                               [--print-debug-intermediate-values]

Evaluate the given implicit white-box implementation

options:
  -h, --help            show this help message and exit
  --input-file INPUT_FILE
                        the file containing the implicit encoded round functions and the external encodings
  --plaintext PLAINTEXT PLAINTEXT
                        the input plaintext given as a hexadecimal representation of the words
  --cancel-external-encodings
                        cancel the external encodings to evaluate on unencoded plaintexts and to obtain unencoded ciphertexts
  --disabled-redundant-perturbations
                        assume the implicit encoded round functions do NOT contain redundant perturbations
  --first-explicit-round FIRST_EXPLICIT_ROUND
                        the Python code describing the first explicit round not included in the implicit round functions
  --last-explicit-round LAST_EXPLICIT_ROUND
                        the Python code describing the last explicit round not included in the implicit round functions
  --output-file OUTPUT_FILE
                        the file to store the output ciphertext and the debug output (default: stdout)
  --print-intermediate-values
                        print intermediate values output while evaluating the implicit implementation
  --print-debug-intermediate-values
                        print debug information while evaluating the implicit round function
```

Thus, to evaluate the previous white-box implementation with cubic implicit rounds of Speck 32/64 for the plaintext `6574 694c`

```
sage -python eval_wb.py --input-file speck32_64_irf --plaintext 6574 694c --first-explicit-round "x = ((x >> 7) | (x << (WORD_SIZE - 7))); x = (x + y) & WORD_MASK;"
```

which will output a variable ciphertext depending on the external encodings (generated in the previous step). The parameter `first-explicit-round` specifies the first round of Speck since this round is not included in the implicit round functions (it does not contain key material). See the [Step 6](#6---the-parameters-first-explicit-round-and-last-explicit-round) for more details about this parameter and `last-explicit-round`.

The white-box implementation can also be evaluated but cancelling the input and output external encoding by

```
sage -python eval_wb.py --input-file speck32_64_irf --plaintext 6574 694c --cancel-external-encodings 
```

which will output the ciphertext `a868 42f2`, which is the expected ciphertext by Speck32/64 with key `1918 1110 0908 0100`.

### 5 - Evaluating the implicit white-box implementation with compiled C code

Alternatively, the white-box implementation (i.e., the implicit round functions) generated in [Step 4](#4---evaluating-the-implicit-white-box-implementation-with-python) can be exported to C code (so that it can be compiled and evaluated faster) with `export_wb.py`.

```
usage: sage -python export_wb.py [-h] [--input-file INPUT_FILE] [--irf-degree {2,3,4}] [--output-file OUTPUT_FILE] [--cancel-external-encodings] [--disabled-redundant-perturbations] [--encoding-mode {hex,bin,bin_zero}]
                                 [--first-explicit-round FIRST_EXPLICIT_ROUND] [--last-explicit-round LAST_EXPLICIT_ROUND] [--print-time-generation] [--debug-file DEBUG_FILE]

Export the given implicit white-box implementation to C code

options:
  -h, --help            show this help message and exit
  --input-file INPUT_FILE
                        the file containing the implicit encoded round functions and the external encodings
  --irf-degree {2,3,4}  the degree of the implicit encoded round functions
  --output-file OUTPUT_FILE
                        the file to store the exported C code
  --cancel-external-encodings
                        cancel the external encodings to evaluate unencoded plaintexts and to obtain unencoded ciphertexts
  --disabled-redundant-perturbations
                        assume the implicit encoded round functions do NOT contain redundant perturbations
  --encoding-mode {hex,bin,bin_zero}
                        the coefficient encoding of the implicit round functions in the exported C code (default: bin)
  --first-explicit-round FIRST_EXPLICIT_ROUND
                        the C code describing the first explicit round not included in the implicit round functions
  --last-explicit-round LAST_EXPLICIT_ROUND
                        the C code describing the last explicit round not included in the implicit round functions
  --print-time-generation
                        print time generation output
  --debug-file DEBUG_FILE
                        the file to store the debug output (default: stdout)
```

The script `export_wb.py` exports the implicit encoded round functions (given by the parameter `input-file`) to a C file or "backend" . The name of this C file can be configured using the `output-file` parameter. After the C backend file is exported, it can be compiled together with `white_box_arx.c` file, an auxiliary file containing the code to evaluate the implicit round functions. Note that `white_box_arx.c` includes the C backend file with the line `#include "white_box_backend.c"`; make sure to update this `include` statement if the `export-file` parameter is changed from the default value.

The `encoding-mode` parameter specifies how the round function data should be encoded in the exported C file. By default, this is done in binary mode, to minimize the size of the output file. However, other options are `hex` (encode in hexadecimal format) and `bin_zero` (encode in binary mode, but escape the null character). These other options might greatly increase the output size (specially `hex`).

Thus, to export the previous white-box implementation with cubic implicit rounds of Speck 32/64, then compile it, and finally evaluate it for the plaintext `6574 694c`

```
sage -python export_wb.py --input-file speck32_64_irf.sobj --irf-degree 3 --first-explicit-round "x = ((x >> 7) | (x << (WORD_SIZE - 7))); x = (x + y) & WORD_MASK;"
gcc -o white_box_arx -lm4ri white_box_arx.c > /dev/null 2>&1
./white_box_arx 6574 694c
```

which will output the same ciphertext (depending on the external encodings) from [Step 4](#4---evaluating-the-implicit-white-box-implementation-with-python). As in [Step 5](#5---evaluating-the-implicit-white-box-implementation-with-compiled-c-code), the parameter `first-explicit-round` specifies the first round of Speck (not included in the implicit round functions as it does not contain key material). See the [Step 6](#6---the-parameters-first-explicit-round-and-last-explicit-round) for more details about this parameter and `last-explicit-round`.

The `gcc` command includes `> /dev/null 2>&1` to suppres all output. This is needed because the default encoding method (`bin`) directly embeds null characters in the exported C file, causing `gcc` to print a warning (that cannot be ignored with `gcc` arguments) that dumps the full binary data to the standard error output. If the `hex` or `bin_zero` modes are used, no warnings will be emitted and it should be safe to compile the C file with output enabled.

### 6 - The parameters first-explicit-round and last-explicit-round

If the first or last rounds of the ARX cipher do not contain key material, these rounds do not need to be encoded (included in the implicit round functions), and they can be given in the Python evaluation or in the C exporting via the parameters `first-explicit-round`and`last-explicit-round`.

For example, for Speck, the round key is not injected in the first round, and this round is not included in the generation of the unencoded affine layers in [Step 1](v#1---setting-the-environment-variables). Thus, this round is not encoded in [Step 3](#3---generating-the-implicit-round-functions), but it is provided as the parameter `first-explicit-round` in the Python evaluation ([Step 4](#4---evaluating-the-implicit-white-box-implementation-with-python)) and in the C exporting ([Step 5](#5---evaluating-the-implicit-white-box-implementation-with-compiled-c-code)).

In the script `eval.py` (`export_wb.py`) for the Python evaluation (C exporting), the parameter `first-explicit-round` is a string containing a snippet of Python (C) code that evaluate the first explicit round, and similarly for `last-explicit-round`. For these snippets of code, you can use the following variables:

- `x` : the first $n/2$ bits of the state.
- `y`: the last $n/2$ bits of the state.
- `WORD_SIZE`: the word size in bits ($n/2$).
- `WORD_MASK`: the integer $2^{n/2}$ that can be used to mask word overflows.

Thus, the input to the explicit rounds can be obtained from the variables `x` and `y`, and the outputs of the explicit rounds needs to be stored in `x` and `y`. The variables `WORD_SIZE` and `WORD_MASK` are read-only.

For example, for Speck 32/64, to implement the first initial round $x, y \mapsto ((x \ggg 7) + y, y)$, the following parameter `first-explicit-round` can be used for both the Python evaluation and the C exporting

`--first-explicit-round "x = ((x >> 7) | (x << (WORD_SIZE - 7))); x = (x + y) & WORD_MASK;"` 
