"""Find exact sign brackets for each individual quotient on the negative real axis."""
from fractions import Fraction
from check_arithmetic import quotient_rows


def sign_at(coeffs, point):
    a, b = point.numerator, point.denominator
    v, scale = coeffs[-1], 1
    for c in reversed(coeffs[:-1]):
        scale *= b
        v = a * v + c * scale
    return (v > 0) - (v < 0)


def negative_half_grid():
    for level in range(140):
        for step in range(32):
            yield Fraction(-64 + step, 64 << level)
    yield Fraction(0)


def main():
    for name, coefficients in zip(('P', 'Q'), quotient_rows()):
        assert tuple(coefficients) == tuple(reversed(coefficients))
        prev, prev_sign = None, 0
        intervals = []
        central_root = sign_at(coefficients, Fraction(-1)) == 0
        for point in negative_half_grid():
            s = sign_at(coefficients, point)
            if not s:
                continue
            if prev_sign and s != prev_sign:
                intervals.append((prev, point))
            prev, prev_sign = point, s
        degree = len(coefficients) - 1
        forced = 2 * len(intervals) + int(central_root)
        print(f'{name} degree={degree} distinct_negative_roots_at_least={forced} center={central_root}', flush=True)
        with open(f'{name}-half-brackets.tsv', 'w') as out:
            out.write('left\tright\n')
            for left, right in intervals:
                out.write(f'{left}\t{right}\n')


if __name__ == '__main__':
    main()
