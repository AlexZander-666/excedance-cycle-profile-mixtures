"""Exact integer check of the printed signs and all 127 ordered half-axis brackets."""

from collections import Counter
from fractions import Fraction
from math import comb
from pathlib import Path


def retained(length):
    return length >= 87 or length in (44, 46, 48, 50, 52, 54, 76, 78, 80, 82, 84, 86)


def eulerian_rows(limit):
    rows = [(1,)]
    for order in range(limit):
        row = rows[-1]
        following = [0] * (order + 2)
        for index, coefficient in enumerate(row):
            following[index] += (index + 1) * coefficient
            following[index + 1] += (order - index) * coefficient
        while following[-1] == 0:
            following.pop()
        rows.append(tuple(following))
    return rows


def pair_types(size):
    assert retained(size)
    assert min(length for length in range(1, size + 1) if retained(length)) == 44
    assert size < 3 * 44
    return [(part, size - part) for part in range(1, size // 2 + 1)
            if retained(part) and retained(size - part)]


def quotients():
    lower_types = pair_types(129)
    upper_types = pair_types(130)
    assert not lower_types
    assert upper_types == [(a, 130 - a) for a in (44, 46, 48, 50, 52, 54)]
    rows = eulerian_rows(129)
    upper = list(rows[129])
    for smaller, larger in upper_types:
        assert smaller < larger
        supports = comb(130, smaller)
        for i, left in enumerate(rows[smaller - 1]):
            for j, right in enumerate(rows[larger - 1]):
                upper[i + j + 1] += supports * left * right
    return {"P": rows[128], "Q": tuple(upper)}


def numerator(row, argument):
    value = row[-1]
    scale = 1
    for coefficient in reversed(row[:-1]):
        scale *= argument.denominator
        value = value * argument.numerator + coefficient * scale
    return value, scale


def check_values(rows):
    argument = Fraction(-1, 9_800_000_000_000_000)
    cases = (
        ("P", rows["P"], 26, -3, -2),
        ("P'", tuple(i * value for i, value in enumerate(rows["P"]) if i), 45, 1, 2),
        ("Q", rows["Q"], 26, 1, 2),
        ("Q'", tuple(i * value for i, value in enumerate(rows["Q"]) if i), 45, 4, 5),
    )
    for name, row, order, lower, upper in cases:
        value, scale = numerator(row, argument)
        assert lower * 10**order * scale < value < upper * 10**order * scale
        print(f"{name}(t*) / 10^{order} in ({lower},{upper})")


def check_brackets(rows):
    lines = Path(__file__).with_name("ordered-brackets.tsv").read_text().splitlines()
    assert lines[0] == "row\tlower_magnitude\tupper_magnitude"
    assert len(lines) == 128
    tags = []
    previous = Fraction(0)
    for line in lines[1:]:
        name, left_text, right_text = line.split("\t")
        left, right = Fraction(left_text), Fraction(right_text)
        assert 0 <= previous <= left < right <= 1
        for endpoint in (left, right):
            assert endpoint.denominator & (endpoint.denominator - 1) == 0
        lo, _ = numerator(rows[name], -left)
        hi, _ = numerator(rows[name], -right)
        assert lo * hi < 0
        tags.append(name)
        previous = right
    assert Counter(tags) == {"P": 63, "Q": 64}
    baseline = list("QP" * 63 + "Q")
    comparisons = enumerate(zip(baseline, tags, strict=True), 1)
    deviations = [(index, expected, found)
                  for index, (expected, found) in comparisons if expected != found]
    assert deviations == [(5, "Q", "P"), (6, "P", "Q")]
    for name, row in rows.items():
        assert row[0] == row[-1] == 1
        assert row == tuple(reversed(row))
        central = int(numerator(row, Fraction(-1))[0] == 0)
        assert central == (name == "P")
        assert 2 * tags.count(name) + central == len(row) - 1 == {"P": 127, "Q": 128}[name]
    print("Half-axis root order:", "".join(tags))
    print("Exactly the stated exchanged tags:", deviations)
    print("Complete counts for P and Q: 127 and 128 distinct negative roots")


rows = quotients()
check_values(rows)
check_brackets(rows)
print("PASS")
