# Requirements
* Python 3
* [SageMath](https://www.sagemath.org/)
* [cryptominisat](https://github.com/msoos/cryptominisat)
* A C compiler (e.g. [gcc](https://gcc.gnu.org/)) (to compile exported C code)
* [m4ri](https://bitbucket.org/malb/m4ri) (to compile exported C code)

# Usage
To execute the scripts in this folder, it is important to first set the `PYTHONPATH` environment variable correctly. It has to be set to the parent folder containing `boolcrypt` and `whiteboxarx` folders. This ensures the `boolcrypt` and `whiteboxarx` libraries can be found by the scripts in this directory. An example for Unix:
```
$ export PYTHONPATH=/path/to/whiteboxarx_parent
$ ls $PYTHONPATH
boolcrypt whiteboxarx ... ...
```

## Generating implicit white-box implementations
The `generate_wb.py` script can be used to generate implicit white-box implementations of ARX ciphers. This script takes some implicit and explicit affine layers as input, encoded in an input file (see the section on Speck for examples), and encodes them using affine or quadratic encodings. The encoded round functions can then be exported to C code, or evaluated using Python.

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
* `trivial-quadratic-encodings` is only used when `irf-degree` is set to 3 or 4
* `trivial-external-encodings` must be set when `mode` is set to `export` (the exported C code does not yet support external encodings)
* `trivial-redundant-perturbations` cannot be combined with `disable-redundant-perturbations`
* `export-file`, `encoding-mode`, `first-explicit-round`, and `last-explicit-round` are only used when `mode` is set to `export`
* `plaintext`, `print-intermediate-values`, and `print-debug-intermediate-values` are only used when `mode` is set to `eval`

After the encoded implicit round functions are generated, `generate_wb.py` enters one of two modes, depending on the `mode` parameter. The default mode is `export`, which exports the encoded implicit round functions to C code. The other mode is `eval`, which evaluates the encoded implicit round functions for some plaintext and outputs the ciphertext, in Python. Currently, only the Speck cipher is supported in `eval` mode.

### Exporting to C code
When the `export` mode is selected, the encoded implicit round functions are exported to a C file or "backend". The name of this file can be configured using the `export-file` parameter. After the C backend file is exported, it can be used in the `white_box_arx.c` file. This code contains all boilerplate to execute arbitrary implicit white-box ARX implementations (using a permuted modular addition in its round function).

Crucially, `white_box_arx.c` includes the C backend file as follows:
```
#include "white_box_backend.c"
```
Make sure to update this `include` if the `export-file` parameter is changed from the default value.

The `encoding-mode` parameter specifies how the round function data should be encoded in the exported C file. By default, this is done in binary mode, to minimize the size of the output file. However, other options are `hex` (encode in hexadecimal format) and `bin_zero` (encode in binary mode, but escape the null character). These other options might greatly increase the output size.

Finally, the `first-explicit-round` and `last-explicit-round` are discussed more in depth in the next section.

### Using the FIRST_EXPLICIT_ROUND and LAST_EXPLICIT_ROUND macros
`generate_wb.py` accepts two parameters, `first-explicit-round` and `last-explicit-round`, which can be used to define some C code. This C code is executed on the input and output words, before and after the implicit round functions are executed, respectively.

The `FIRST_EXPLICIT_ROUND` and `LAST_EXPLICIT_ROUND` macros are defined in the exported C file as follows:
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

For example, for `Speck32/64`, the following `first-explicit-round` parameter could be used:
```
--first-explicit-round "x = ((x >> 7) | (x << (WORD_SIZE - 7))); x = (x + y) & WORD_MASK;"
```
This corresponds to a right circular bitshift by 7 positions of `x`, followed by a modular addition of `x` and `y`. 

For example, for `Speck64/128` or `Speck128/256`, the following `first-explicit-round` parameter could be used:
```
--first-explicit-round "x = ((x >> 8) | (x << (WORD_SIZE - 8))); x = (x + y) & WORD_MASK;"
```
Here, the alpha value is 8.

The `last-explicit-round` parameter can always be left omitted for Speck.

### Evaluating implicit white-box implementation
When the `eval` mode is selected, the encoded implicit round functions are evaluated in Python. This mode only supports the Speck block cipher. The `plaintext` parameter specifies the plaintext to evaluate. Debug information and intermediate round values can be displayed using the `print-intermediate-values` and `print-debug-intermediate-values` parameters.

## Example: implicit white-box Speck implementations
The `speck.py` script contains an example implementation to generate the (unencoded) implicit and explicit affine layers for the Speck block cipher. It can be invoked from the command line to save these affine layers to a file. This output file can then be used as an argument for `generate_wb.py` to generate an implicit white-box Speck implementation.

`speck.py` can be executed using SageMath as follows:
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

For example, the following command will generate the implicit and explicit affine layers for a `Speck32/64` instance using the [test vectors key][1] and store it in `speck32_64_affine_layers.sobj`:
```
$ sage -python speck.py --block-size 32 --output-file speck32_64_affine_layers.sobj 1918 1110 0908 0100
```

Then, `generate_wb.py` can be used to read the `speck32_64_affine_layers.sobj` file and export a C "backend" file containing the encoded implicit round functions. The following example uses quadratic implicit round functions (the fastest to generate), trivial external encodings, and saves the output to `white_box_backend.c`:
```
$ sage -python generate_wb.py --mode export --input-file speck32_64_affine_layers.sobj --irf-degree 2 --seed 3141592653589793238 --trivial-external-encodings --print-time-generation --export-file white_box_backend.c --first-explicit-round "x = ((x >> 7) | (x << (WORD_SIZE - 7))); x = (x + y) & WORD_MASK;"
```

This command will take some time to execute. When the command is finished, a file called `white_box_backend.c` will be present in the current working directory. By default, `white_box_backend.c` is included in the `white_box_arx.c`. Thus, the final step in creating an executable implicit white-box Speck implementation is to compile this C file:
```
$ gcc -o white_box_arx -lm4ri white_box_arx.c > /dev/null 2>&1
```
Note that this command suppresses all output from `gcc`. This is needed because the default encoding method (`bin`) directly embeds null characters in the exported C file. This causes `gcc` to print a warning which prints the full binary data to the standard error output. This warning cannot be suppressed. If the `hex` or `bin_zero` modes are used, no warnings will be emitted and it should be safe to compile the C file with output enabled.

Then `white_box_arx` can be executed with any arbitrary plaintext as arguments (taken from [test vectors][1]):
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
Once again, this results in the expected output.

[1]: https://eprint.iacr.org/2013/404
