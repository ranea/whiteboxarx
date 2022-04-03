# Implicit White-box Implementations of ARX Ciphers

Generate implicit white-box implementations of ARX ciphers following the method described in the paper [Implicit White-Box Implementations: White-Boxing ARX Ciphers](https://eprint.iacr.org/2022/XXX).

## Requirements

* Python 3
* [BoolCrypt](https://github.com/ranea/boolcrypt)
* [SageMath](https://www.sagemath.org/) equipped with [CryptoMiniSat](https://github.com/msoos/cryptominisat)
* [gcc](https://gcc.gnu.org/) or another C compiler (to compile exported C code)
* [M4RI](https://bitbucket.org/malb/m4ri) (to compile exported C code)

## Usage

To execute the scripts in this folder, the environment variable `PYTHONPATH` should contain the directory containing `generate_wb.py` and the directory of `boolcrypt`, so that the `boolcrypt` library and the scripts in `whiteboxarx` can be located. In a virtual environment, [add2virtualenv](https://virtualenvwrapper.readthedocs.io/en/latest/command_ref.html#add2virtualenv) can be used to add folders to the `PYTHONPATH`.

### Generating implicit white-box implementations

The `generate_wb.py` generates an implicit white-box implementation of a given ARX cipher. The cipher is given in an input file containing the (unencoded) affine layers (of each round) in implicit form and explicit form (see also the last section *Example*).  Currently, `generate_wb.py` only supports ARX ciphers where the non-linear layer of each round is the permuted modular addition.

The script `generate_wb.py` builds in an automated way the encoded round functions composing the white-box implementation, and the white-box implementation can be either exported to C code or evaluated using Python code.

`generate_wb.py` can be executed using SageMath as follows:

```
$ sage -python generate_wb.py -h
usage: sage -python generate_wb.py [-h] [--mode {export,eval}] [--input-file INPUT_FILE] [--debug-file DEBUG_FILE] [--irf-degree {2,3,4}] [--seed SEED] [--trivial-affine-encodings] [--trivial-quadratic-encodings] [--trivial-external-encodings]
                                   [--trivial-redundant-perturbations] [--trivial-graph-automorphisms [{repeat}]] [--disable-redundant-perturbations] [--ensure-max-degree] [--print-time-generation] [--print-debug-generation] [--export-file EXPORT_FILE]
                                   [--encoding-mode {hex,bin,bin_zero}] [--first-explicit-round FIRST_EXPLICIT_ROUND] [--last-explicit-round LAST_EXPLICIT_ROUND] [--plaintext PLAINTEXT [PLAINTEXT ...]] [--print-intermediate-values] [--print-debug-intermediate-values]

Generate implicit white-box implementations of ARX ciphers

options:
  -h, --help            show this help message and exit
  --mode {export,eval}  the mode to use: 'export' exports the generated implementation to C code, 'eval' evaluates it in Python (default: export)
  --input-file INPUT_FILE
                        the file used to store the (unencoded) implicit and explicit affine layers (default: stored_affine_layers.sobj)
  --debug-file DEBUG_FILE
                        the file used to store the debug output (default: stdout)
  --irf-degree {2,3,4}  the degree of the encoded implicit round functions (default: 2)
  --seed SEED           the seed used to generate random values (default: a random value)
  --trivial-affine-encodings
                        use trivial affine encodings
  --trivial-quadratic-encodings
                        use trivial quadratic encodings
  --trivial-external-encodings
                        use trivial external encodings
  --trivial-redundant-perturbations
                        use trivial redundant perturbations
  --trivial-graph-automorphisms [{repeat}]
                        use trivial graph automorphisms (if set to 'repeat', the same graph automorphism is used for each round)
  --disable-redundant-perturbations
                        disable redundant perturbations
  --ensure-max-degree   ensure that the encoded implicit round functions have maximum degree
  --print-time-generation
                        print time generation output
  --print-debug-generation
                        print debug information output
  --export-file EXPORT_FILE
                        the file used to store the exported C code (default: white_box_backend.c)
  --encoding-mode {hex,bin,bin_zero}
                        how to store the encoded implicit round functions in the exported C code (default: bin)
  --first-explicit-round FIRST_EXPLICIT_ROUND
                        C code describing the first explicit round; refer to README.md for examples (default: )
  --last-explicit-round LAST_EXPLICIT_ROUND
                        C code describing the last explicit round; refer to README.md for examples (default: )
  --plaintext PLAINTEXT PLAINTEXT
                        the plaintext to use to evaluate the implicit implementation, a hexadecimal representation of the words (default: None)
  --print-intermediate-values
                        print intermediate values output while evaluating the implicit implementation
  --print-debug-intermediate-values
                        print intermediate values output while evaluating the implicit round function
```

When executed, `generate_wb.py` always generates the encoded implicit round functions first. This process can be customized using the many parameters described above. Of particular importance is the `input-file` parameter, which must contain a pickled (using SageMath's `save` function) tuple of implicit and explicit affine layers. Additional debugging information can be output using `print-time-generation` and `print-debug-generation`, and saved using `debug-file`.

Notably, there are also some restrictions on the parameters:

* `trivial-quadratic-encodings` is only used when `irf-degree` is set to 3 or 4; if enabled, the round encodings only contain affine permutations and not affine-quadratic self-equivalences 
* the additional countermesaure based on redundant perturbations can be disabled with `disable-redundant-perturbations`, and if enabled trivial redudant perturbations are used if `trivial-redundant-perturbations` (but these two parameters cannot be comined)
* `export-file`, `encoding-mode`, `first-explicit-round`, and `last-explicit-round` are only used when `mode` is set to `export`
* `plaintext`, `print-intermediate-values`, and `print-debug-intermediate-values` are only used when `mode` is set to `eval`

For large blocksizes `generate_wb.py` can take several hours due to the generation of graph automorphisms and quadratic encodings (i.e., affine-quadratic self-equivalences).

After the encoded implicit round functions are generated, `generate_wb.py` enters one of two modes depending on the `mode` parameter: 

- If `--mode export` (default), the implicit white-box implementation is exported to C code (explained below).

- If `--mode eval`, the implicit white-box implementation is evaluated for the given `plaintext` using Python code, where debug information and intermediate round values can be displayed using the `print-intermediate-values` and `print-debug-intermediate-values` parameters. While the Speck cipher is used by default in the `eval` mode, by modifying the last part of `generate_wb.py` a different cipher can be used.

### Exporting to C code

When the `export` mode is selected, the encoded implicit round functions are exported to a C file or "backend". The name of this file can be configured using the `export-file` parameter. After the C backend file is exported, it can be used in the `white_box_arx.c` file. This code contains all boilerplate to execute arbitrary implicit white-box ARX implementations (using a permuted modular addition in its round function).

Crucially, `white_box_arx.c` includes the C backend file as follows:

```
#include "white_box_backend.c"
```

Make sure to update this `include` statement if the `export-file` parameter is changed from the default value.

The `encoding-mode` parameter specifies how the round function data should be encoded in the exported C file. By default, this is done in binary mode, to minimize the size of the output file. However, other options are `hex` (encode in hexadecimal format) and `bin_zero` (encode in binary mode, but escape the null character). These other options might greatly increase the output size.

Currently, if external encodings are used, the inverse of the external encodings is not output by `generate_wb.py`.

##### The C macros FIRST_EXPLICIT_ROUND and LAST_EXPLICIT_ROUND

If the first and/or last rounds of the cipher don't contain key material, it is also possible to not encode these rounds and implement them explicitly in the C code. To do so, omit these rounds in the `INPUT_FILE`  and add these rounds in the parameters `first-explicit-round`and`last-explicit-round`.

The parameters `first-explicit-round` and `last-explicit-round` define the C code macros `FIRST_EXPLICIT_ROUND` and `LAST_EXPLICIT_ROUND` that are executed before and after the implicit round functions are executed, respectively. The `FIRST_EXPLICIT_ROUND` and `LAST_EXPLICIT_ROUND` macros are defined in the exported C file as follows:

```
#define FIRST_EXPLICIT_ROUND(x, y) {first_explicit_round}
#define LAST_EXPLICIT_ROUND(x, y) {last_explicit_round}
```

The following variables can be used in the `FIRST_EXPLICIT_ROUND` and `LAST_EXPLICIT_ROUND` macros:

```
USE_REDUNDANT_PERTURBATIONS // whether redundant permutations are used
MAX_DEGREE                  // the maximum degree of the encoded implicit round functions
ROUNDS                      // the number of encoded implicit round functions
WORD_SIZE                   // the word size in bits
WORD_TYPE                   // the C type used to represent a word
WORD_IN_TYPE                // the C type used to input a word
WORD_OUT_TYPE               // the C type used to output a word
WORD_CONSTANT_TYPE          // the C type used to embed a constant word value
WORD_MASK                   // a value that can be used to mask word overflows
MONOMIAL_WORD_TYPE          // the C type used to represent a monomial word
MONOMIAL_WORD_SIZE          // the monomial word size in bits 
```

## Example

In this section we describe step-by-step how to generate an implicit white-box implementation of Speck.

The first step is to generate an input file containing the affine layers (of each round) in implicit form and explicit form of Speck. This is done by the script `speck.py`, which can be invoked from the command line to save these affine layers to a file as follows:

```
$ sage -python speck.py -h
usage: sage -python speck.py [-h] [--block-size [{8,32,64,128}]] [--output-file [OUTPUT_FILE]] key [key ...]

Generate (unencoded) implicit and explicit affine layers of Speck instances

positional arguments:
  key                   the key to use for the affine layers, a hexadecimal representation of the words

options:
  -h, --help            show this help message and exit
  --block-size [{8,32,64,128}]
                        the block size in bits of the Speck instance (default: 128)
  --output-file [OUTPUT_FILE]
                        the file used to store the (unencoded) implicit and explicit affine layers (default: stored_affine_layers.sobj)
```

Thus, we first generate the implicit and explicit affine layers of `Speck32/64` using the [test vectors key][1] and store it in `speck32_64_affine_layers.sobj` by

```
$ sage -python speck.py --block-size 32 --output-file speck32_64_affine_layers.sobj 1918 1110 0908 0100
```

Then, we generate an implicit implementation of Speck32/64 for the previous key, using quadratic implicit round functions (the fastest to generate) and trivial external encodings by

```
$ sage -python generate_wb.py --mode export --input-file speck32_64_affine_layers.sobj --irf-degree 2 --seed 3141592653589793238 --trivial-external-encodings --print-time-generation --export-file white_box_backend.c --first-explicit-round "x = ((x >> 7) | (x << (WORD_SIZE - 7))); x = (x + y) & WORD_MASK;"
```

Note the first round of Speck is given in the argument `--first-explicit-round "x = ((x >> 7) | (x << (WORD_SIZE - 7))); x = (x + y) & WORD_MASK;` since the first round of Speck doesn't contain key material and it is not included in the output of `speck.py`.

This command will take some time to execute. When the command is finished, a file called `white_box_backend.c` will be present in the current working directory. 

The last step is to create an executable by compile this C file and `white_box_arx.c`:

```
$ gcc -o white_box_arx -lm4ri white_box_arx.c > /dev/null 2>&1
```

Note that this command suppresses all output from `gcc`. This is needed because the default encoding method (`bin`) directly embeds null characters in the exported C file. This causes `gcc` to print a warning which prints the full binary data to the standard error output. This warning cannot be suppressed. If the `hex` or `bin_zero` modes are used, no warnings will be emitted and it should be safe to compile the C file with output enabled.

To evaluate the executable `white_box_arx`, simply provide the plaintext (here taken from [test vectors][1]) as argument: 

```
$ ./white_box_arx 6574 694c
a868 42f2
```

The ciphertext is output to the standard output, in this case the expected test vector ciphertext.

Alternatively, the `eval` mode could be used to execute the implicit white-box Speck implementation directly in Python:

```
$ sage -python generate_wb.py --mode eval --input-file speck32_64_affine_layers.sobj --irf-degree 2 --seed 3141592653589793238 --trivial-external-encodings --print-time-generation --plaintext 6574 694c
...
Evaluating implicit white-box implementation with input (6574, 694c)


Ciphertext = (a868, 42f2)
```

[1]: https://eprint.iacr.org/2013/404
