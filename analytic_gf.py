#!/usr/bin/env python3
"""
Translate the grammar directly into generating-function equations and solve
them with SymPy.

Rules:
- union -> +
- concatenation -> *
- size means "number of digits used"
- only digits contribute size, so each digit contributes z
- operators, decimal points, and parentheses contribute size 0
"""

from __future__ import annotations

import argparse
import math

import sympy as sp
GRAMMAR = """\
expr -> <number> | <sum> | <product> | <quotient>
<sum> -> <term> + <term> | <term> - <term> | <sum> + <term> | <sum> - <term>
<term> -> <number> | <product> | <quotient>
<product> -> <factor> x <factor> | <product> x <factor> | (<quotient>) x <factor>
<quotient> -> <factor> / <factor> | <product> / <factor> | (<quotient>) / <factor>
<factor> -> <number> | (<sum>)
<number> -> <digit>
"""

NUMBER_GRAMMAR = {
    "a":
    "<number> -> <digit>",
    "b":
    "<number> -> <digit> | <number><digit>",
    "c-old":
    "<number> -> <digit string> | .<digit string>\n<digit string> -> <digit> | <digit string><digit>",
    "c-errata":
    "<number> -> <digit string> | .<digit string> | <digit string>.<digit string>\n<digit string> -> <digit> | <digit string><digit>",
}


def schroeder_numbers(limit: int) -> list[int]:
	vals = [0]*(limit+1)
	vals[0] = 1
	for n in range(1, limit+1):
		vals[n] = vals[n-1]
		for k in range(n):
			vals[n] += vals[k]*vals[n-1-k]
	return vals


def compositions(total: int, parts: int):
	if parts==1:
		yield (total, )
		return
	for first in range(1, total-parts+2):
		for rest in compositions(total-first, parts-1):
			yield (first, )+rest


def block_weight(mode: str, length: int) -> int:
	if mode=="a":
		return 1 if length==1 else 0
	if mode=="b":
		return 1
	if mode=="c-old":
		return 2
	if mode=="c-errata":
		return length+1
	raise ValueError(f"unknown mode: {mode}")


def combinatorial_count(mode: str, n: int) -> int:
	schr = schroeder_numbers(n-1)
	total = 0
	for k in range(n):
		# E(z) = A(z) R(2A(z)) = sum_{k>=0} 2^k S_k A(z)^(k+1)
		tree_weight = (2**k)*schr[k]
		block_total = 0
		for comp in compositions(n, k+1):
			w = 1
			for length in comp:
				w *= block_weight(mode, length)
			block_total += w
		total += tree_weight*block_total
	return total


def unrestricted_count(mode: str, n: int) -> int:
	vals = [0]*(n+1)
	for m in range(1, n+1):
		vals[m] = block_weight(mode, m)
		for left in range(1, m):
			vals[m] += 4*vals[left]*vals[m-left]
	return vals[n]


def main() -> None:
	parser = argparse.ArgumentParser()
	parser.add_argument(
	    "--mode",
	    choices=("a", "b", "c-old", "c-errata", "all"),
	    default="all",
	)
	parser.add_argument("--max-n", type=int, default=9)
	args = parser.parse_args()

	z = sp.symbols("z")
	expr, sum_, term, prod, quot, factor, number, digit_string = sp.symbols(
	    "expr sum term prod quot factor number digit_string")
	free_expr = sp.symbols("free_expr")

	print("Grammar:")
	print(GRAMMAR.rstrip())
	print()

	modes = ("a", "b", "c-old",
	         "c-errata") if args.mode=="all" else (args.mode, )
	for mode in modes:
		helper_pairs = []
		number_expr = z

		print(f"mode={mode}")
		print("grammar:")
		print(GRAMMAR.rstrip())
		if mode!="a":
			print()
			print("number extension:")
			print(NUMBER_GRAMMAR[mode])
		print()

		if mode=="b":
			number_expr = digit_string
			helper_pairs = [
			    (digit_string, z+z*digit_string),
			]
		elif mode=="c-old":
			number_expr = number
			helper_pairs = [
			    (digit_string, z+z*digit_string),
			    (number, digit_string+digit_string),
			]
		elif mode=="c-errata":
			number_expr = number
			helper_pairs = [
			    (digit_string, z+z*digit_string),
			    (number, digit_string+digit_string+digit_string*digit_string),
			]

		grammar_pairs = [
		    (expr, number_expr+sum_+prod+quot),
		    (sum_, term*term+term*term+sum_*term+sum_*term),
		    (term, number_expr+prod+quot),
		    (prod, factor*factor+prod*factor+quot*factor),
		    (quot, factor*factor+prod*factor+quot*factor),
		    (factor, number_expr+sum_),
		]
		eqs = [
		    sp.Equality(lhs, rhs) for lhs, rhs in helper_pairs+grammar_pairs
		]

		unknowns = [expr, sum_, term, prod, quot, factor]
		if any(lhs==number for lhs, _ in helper_pairs):
			unknowns.insert(0, number)
		if any(lhs==digit_string for lhs, _ in helper_pairs):
			unknowns.insert(0, digit_string)

		sols = sp.solve(eqs, unknowns, dict=True)
		analytic = None
		for sol in sols:
			candidate = sp.simplify(sol[expr])
			if sp.simplify(candidate.subs(z, 0))==0:
				analytic = candidate
				break
		if analytic is None:
			raise RuntimeError(f"no analytic branch found for mode={mode}")

		number_closed = number_expr
		if helper_pairs:
			helper_eqs = [sp.Equality(lhs, rhs) for lhs, rhs in helper_pairs]
			helper_solution = sp.solve(helper_eqs,
			                           [lhs for lhs, _ in helper_pairs],
			                           dict=True)[0]
			number_closed = sp.simplify(number_expr.subs(helper_solution))

		print("number equations:")
		for lhs, rhs in helper_pairs:
			print("  ", sp.simplify(lhs), "=", sp.simplify(rhs))
		print("grammar equations:")
		for lhs, rhs in grammar_pairs:
			print("  ", sp.simplify(lhs), "=", sp.simplify(rhs))
		print("closed grammar <number>(z) =", sp.factor(number_closed))
		print("closed grammar <expression>(z) =", sp.factor(analytic))
		print("coefficients:")
		for n in range(1, args.max_n+1):
			series = sp.expand(analytic.series(z, 0, n+1).removeO())
			gf_count = int(series.coeff(z, n))
			comb_count = combinatorial_count(mode, n)
			print(f"  n={n} gf_count={gf_count} comb_count={comb_count}")
		unrestricted_atom = sp.simplify(number_closed)
		unrestricted_eq = sp.Equality(free_expr,
		                              unrestricted_atom+4*free_expr**2)
		unrestricted_solutions = sp.solve(unrestricted_eq,
		                                  free_expr,
		                                  dict=True)
		unrestricted_expr = None
		for sol in unrestricted_solutions:
			candidate = sp.simplify(sol[free_expr])
			if sp.simplify(candidate.subs(z, 0))==0:
				unrestricted_expr = candidate
				break
		if unrestricted_expr is None:
			raise RuntimeError(
			    f"no unrestricted analytic branch found for mode={mode}")
		print()
		print("unrestricted binary parenthesization model:")
		print("  leaf GF = grammar <number>(z)")
		print("  <number>(z) =", sp.factor(unrestricted_atom))
		print("  F(z) = <number>(z) + 4*F(z)^2")
		print("closed unrestricted F(z) =", sp.factor(unrestricted_expr))
		print("unrestricted coefficients:")
		for n in range(1, args.max_n+1):
			series = sp.expand(unrestricted_expr.series(z, 0, n+1).removeO())
			gf_count = int(series.coeff(z, n))
			comb_count = unrestricted_count(mode, n)
			print(f"  n={n} gf_count={gf_count} comb_count={comb_count}")
		print()


if __name__=="__main__":
	main()
