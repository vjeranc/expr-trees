# expr-trees

Copyright (C) 2026 Vjeran Crnjak

License: GPL-3.0-only

## Toolchain

Tested locally on Arch Linux with:
- `gcc 15.2.1+r447+g6a64f6c3ebb8-1`
- `boost 1.89.0-4`

## Scope

This repo checks numbers from TAOCP 4A, answers to exercises 122 and 123.

Main files:
- `fast_target_counter.cpp`: fast target counter.
- `representable_integers.cpp`: counts all reachable integers.
- `shape_count.cpp`: counts grammar shapes.
- `analytic_gf.py`: counts grammar shapes much faster, directly from grammar def.
- `openmp_bruteforce_representable.cpp`: exhaustive OpenMP evaluator over the precedence grammar.
- `openmp_catalan_representable.cpp`: exhaustive OpenMP evaluator over all binary parenthesizations.
- `openmp_bruteforce_witnesses.cpp`: exhaustive OpenMP evaluator that writes one shortest witness per reachable integer.

## Results

Confirmed target counts for `=100`:
- 122(a): `1641`
- 122(b): `3366`
- 122(c), [errata](https://www-cs-faculty.stanford.edu/~knuth/err4a.tex) grammar: `137375`

Confirmed extra counts with leading minus:
- 122(a): `1362`
- 122(b): `2759`
- 122(c), [errata](https://www-cs-faculty.stanford.edu/~knuth/err4a.tex) grammar: `116222`

Leading minus is just `-(E)=100`, so it is the same as solving `E=-100`.

Confirmed smallest unreachable positive integers:
- 123(a): `2284`
- 123(b): `6964`
- 123(c), old dot-only grammar: `14786`

Confirmed counts of representable integers:
- 123(a): `27666`
- 123(b): `136607`
- 123(c): we get `218438`

There is still an off by one in representable integers.
[errata](https://www-cs-faculty.stanford.edu/~knuth/err4a.tex) says `218439`.
Three independent exhaustive programs gave `218438`:
- `representable_integers.cpp`
- `openmp_bruteforce_representable.cpp`
- `openmp_catalan_representable.cpp`

The unrestricted Catalan program traversed exactly
`F_9 = 74,323,639,466` formal expressions and still gave `218438`.

Old fascicle numbers are reproduced.
Examples: `14786` for old 123(c), and the
pre-[errata](https://www-cs-faculty.stanford.edu/~knuth/err4a.tex) grammar for
dot-only numbers.

## Grammar

```text
expr -> <number> | <sum> | <product> | <quotient>
<sum> -> <term> + <term> | <term> - <term> | <sum> + <term> | <sum> - <term>
<term> -> <number> | <product> | <quotient>
<product> -> <factor> x <factor> | <product> x <factor> | (<quotient>) x <factor>
<quotient> -> <factor> / <factor> | <product> / <factor> | (<quotient>) / <factor>
<factor> -> <number> | (<sum>)
<number> -> <digit>

(b) extends number with:
<number> -> <digit> | <number><digit>

(c) extends number with ([errata](https://www-cs-faculty.stanford.edu/~knuth/err4a.tex)):
<number> -> <digit string> | .<digit string> | <digit string>.<digit string>
<digit string> -> <digit> | <digit string><digit>
```

Precedence and associativity alone are not enough to get least number of
interesting expressions. That grammar is a superset of DEK's grammar. For
example, `1-(2-3)` is the same as `1-2+3`. Also `7/(8*9)` is the same as
`7/8/9`. DEK's grammar eliminates more "repeat" expressions.

## Performance

`fast_target_counter.cpp` runs on 122(c), target `100`, in about `28s` on an
AMD Ryzen 5 5600X with `4x32 GiB G.Skill F4-3200C14-32GTRG @ 3200 MT/s`, built
with `g++ (GCC) 15.2.1`.

The OpenMP exhaustive checkers keep little state in memory: no global witness
tables, no expression strings in the count-only runs, and only thread-local
integer sets/maps that are merged at the end.

Observed runtimes on the same machine:
- `openmp_bruteforce_representable.cpp`, 123(c), errata grammar, 12 threads:
  about `65s`
- `openmp_bruteforce_witnesses.cpp`, same search plus shortest witnesses:
  `189.111s`
- `openmp_catalan_representable.cpp`, unrestricted `F_9 = 74,323,639,466`
  parenthesizations, 12 threads: about `10-11 min`

DEK likely has a better algorithm.
[errata](https://www-cs-faculty.stanford.edu/~knuth/err4a.tex) is from 2008,
and DEK's code seems to handle these counts much more easily than our current
programs. 28 seconds today in 2026 implies many more in 2008, so
`fast_target_counter.cpp` is a bit slow.

## Analytic Combinatorics

Since 2012 I have played with this problem. I first heard of it in "Diskontna
matematika 1" course at FER, a play on Concrete Mathematics. If we extrapolate
further, it will take me centuries if not millenia to go through all of
the exercises in TAOCP.

Only later I found that this is a Dudeney's Digital Century puzzle problem
solved by DEK in TAOCP 4A.

I counted these objects through brute force generation.
That eventually led to using Mathematica on integer sequences, just to guess
generating functions from the counts.

Later I worked through the Coursera course on Analytic Combinatorics.
That makes this much cleaner: write the grammar, translate productions to
equations, solve the system, then read off coefficients.
A small SymPy script does exactly that:
- `analytic_gf.py`

It starts from the grammar, writes equations for the nonterminals, solves for
`<expression>(z)`, and expands coefficients.

The key translation is:
- union becomes `+`
- concatenation becomes `*`
- only digits contribute size, so each digit is `z`
- operators and parentheses have size `1`

For errata `(c)` the script prints:
- `digit_string = z*(digit_string + 1)`
- `number = digit_string*(digit_string + 2)`
- `expr = number + prod + quot + sum`
- `sum = 2*term*(sum + term)`
- `term = number + prod + quot`
- `prod = factor*(factor + prod + quot)`
- `quot = factor*(factor + prod + quot)`
- `factor = number + sum`

and then:
- `closed <number>(z) = -z*(z - 2)/(z - 1)^2`
- `closed <expression>(z) = (3*z^2 - 6*z - sqrt(17*z^4 - 68*z^3 + 82*z^2 - 28*z + 1) + 1) / (4*(z - 1)^2)`
- `n=9 gf_count=9875514250 comb_count=9875514250`


This is `10` more than DEK's amended `9,875,514,240`.
The likely reason: the symbolic grammar count includes all `10` top-level
`<number>` expressions that use all nine digits and no operator: `.123456789`,
`123456789`, `1.23456789`, ..., `12345678.9`. DEK's reported case count seems
to exclude these trivial no-operator cases.
I believe there are also libraries which will spit out efficient lexicographic
enumeration algorithms as well. But when it comes to the actual problem of
exercise 122, enumeration is not a fast approach.

Script also prints the unrestricted binary-parenthesization model

- `F(z) = <number>(z) + 4*F(z)^2`

which yields

- `n=9 gf_count=74323639466 comb_count=74323639466`

easy to predict total runtime of bruteforce.

## Notes

The code can also be extended to keep witnesses.
That would let it print shortest, longest, or all expressions of interest.
Left as an exercise to the reader.
