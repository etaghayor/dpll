# DPLL
An implementation of the DPLL algorithm.

## Goal
The goal of this mini-project was to implement a recursive DPLL solver in Ocaml.
The main functions written in the file dpll.ml were:

 - The function simplifie : int -> int list list -> int list list option
 - The function unitaire : int list list -> int option
 - The function pur : int list list -> int option
 - The function solveur_dpll_rec : int list list -> int list -> int list option
 - The functions pretty_print_* : int list list -> int list -> unit

## Testing the solver

 First, you can use the makefile by calling:

  ``$ make``

to compile a native executable and to test it on files with DIMACS format. </br>
The test files are included in ```tests``` directory.

  ```$ ./dpll tests/SAT/sudoku-4x4.cnf``` </br>
  ```$ ./dpll tests/UNSAT/systeme.cnf```

## DISCLAIMER:
- All functions and files other than the ones listed in the first part and
their auxiliary subfunctions were given to us by our [professor, Mr Schmitz](https://www.irif.fr/en/users/schmitz/index). </br>
- This is the final result of a project carried out by two people and all change states and their contributor are ignored.
