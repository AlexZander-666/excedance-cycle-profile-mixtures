"""Recompute the two quotient signs from the alternating binomial Eulerian formula."""
from fractions import Fraction
from functools import cache
import hashlib
from math import comb

POINT = Fraction(-1, 9_800_000_000_000_000)
SHORTER_LENGTHS = (44, 46, 48, 50, 52, 54)


@cache
def eulerian(n):
    return tuple(sum((-1)**j * comb(n + 1, j) * (k + 1 - j)**n
                     for j in range(k + 2))
                 for k in range(n))


def quotient_rows():
    lower = eulerian(128)
    upper = list(eulerian(129))
    for shorter in SHORTER_LENGTHS:
        multiplicity = comb(130, shorter)
        for i, left in enumerate(eulerian(shorter - 1)):
            for j, right in enumerate(eulerian(129 - shorter)):
                upper[1 + i + j] += multiplicity * left * right
    return lower, upper


def evaluate_and_differentiate(coefficients):
    value = derivative = Fraction(0)
    for coefficient in reversed(coefficients):
        derivative = derivative * POINT + value
        value = value * POINT + coefficient
    return value, derivative


def main():
    for name, sign, row in zip(("P", "Q"), (-1, 1), quotient_rows(), strict=True):
        value, derivative = evaluate_and_differentiate(row)
        assert sign * value > 0 and derivative > 0
        print(f"{name} degree={len(row) - 1} signs=({sign:+d},+1)")
        print(f"  value≈{float(value):.12g} derivative≈{float(derivative):.12g}")
        digest = hashlib.sha256(",".join(map(str, row)).encode()).hexdigest()
        print(f"  ascending_coefficients_sha256={digest}")
    print("PASS exact rational arithmetic")


if __name__ == "__main__":
    main()
