# Notes

## Validated counts

- `123(c)` errata representable integers: `218438`
- errata smallest unreachable positive: `14786`

These were confirmed by:

- `representable_integers.cpp`
- `openmp_bruteforce_representable.cpp`
- `openmp_catalan_representable.cpp`

## Timings

- `openmp_bruteforce_representable.cpp`
  - `n=8`, `mode=c`, `c_style=errata`, `threads=12`: `elapsed=4.02s`
  - `n=9`, `mode=c`, `c_style=errata`, `threads=12`: about `65s`

- `openmp_catalan_representable.cpp`
  - `n=8`, `mode=c`, `c_style=errata`, `threads=12`: `elapsed=31.15s`
  - `n=9`, `mode=c`, `c_style=errata`, `threads=12`: about `10-11 min`

## Exhaustive unrestricted run

- `F_9 = 74323639466`
- `syntax_attempts = 74323639466`
- `valid_exprs = 74276748302`
- `representable_integers = 218438`
