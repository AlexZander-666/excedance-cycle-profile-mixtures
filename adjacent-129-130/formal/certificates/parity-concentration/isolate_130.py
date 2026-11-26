"""Certify the individual true quotient roots using reciprocity and dyadic sign brackets."""
from fractions import Fraction
from pathlib import Path
import runpy

quotients = runpy.run_path(str(Path(__file__).parent.parent / "two-cycle-130/check_arithmetic.py"))["quotient_rows"]


def sign(coefficients, x):
    """Sign of P(-x), multiplied by the strictly positive dyadic denominator to its degree."""
    exponent = x.denominator.bit_length() - 1
    assert x.denominator == 1 << exponent
    value = coefficients[-1]
    for i, coefficient in enumerate(reversed(coefficients[:-1]), 1):
        value = (coefficient << (exponent * i)) - value * x.numerator
    return (value > 0) - (value < 0)


def bracket(coefficients):
    assert list(coefficients) == list(reversed(coefficients))
    degree = len(coefficients) - 1
    points = sorted({Fraction(0), Fraction(1)} | {
        Fraction(32 + a, 32 << e) for a in range(32) for e in range(1, 146)
    })
    previous = None
    pairs = []
    for x in points:
        s = sign(coefficients, x)
        if not s:
            continue
        if previous is not None and s != previous[1]:
            pairs.append((previous[0], x))
        previous = x, s
    midpoint = int(sign(coefficients, Fraction(1)) == 0)
    return degree, midpoint, pairs


if __name__ == "__main__":
    for name, row in zip(("P", "Q"), quotients(), strict=True):
        degree, midpoint, pairs = bracket(row)
        assert (degree, midpoint) == {"P": (127, 1), "Q": (128, 0)}[name]
        assert 2 * len(pairs) + midpoint == degree
        assert all(0 <= left < right <= 1 for left, right in pairs)
        assert all(a[1] <= b[0] for a, b in zip(pairs, pairs[1:]))
        print(name, "degree", degree, "brackets in (-1,0)", len(pairs), "root -1", midpoint,
              "distinct negative roots certified", 2 * len(pairs) + midpoint)
        for left, right in pairs:
            print(name, left, right)
