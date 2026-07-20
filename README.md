# ECC
A Lean 4 project depending on [cslib](https://github.com/leanprover/cslib) and [mathlib](https://github.com/leanprover-community/mathlib4) (transitively).

Goal is to formalize Error Correction Codes in Lean.

## Prereqs

You need [elan](https://github.com/leanprover/elan) installed.

## Building
```sh
git clone https://github.com/wurtylex/Lean-Formalization-of-Error-Correction-Codes-
cd Lean-Formalization-of-Error-Correction-Codes-
lake exe cache get
lake build
```

## References
The primary reference for this project is:

- Venkatesan Guruswami, Atri Rudra, and Madhu Sudan, *Essential Coding Theory*. [PDF](https://cse.buffalo.edu/faculty/atri/courses/coding-theory/book/web-coding-book.pdf)

Unless stated otherwise, definitions and statements follow the conventions of that book.

## Project Layout
TODO
