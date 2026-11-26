"""Generate full-axis dyadic sign meshes and the finite Lean data."""
from fractions import Fraction
from pathlib import Path
from check_arithmetic import quotient_rows
from individual_roots import negative_half_grid, sign_at


def grid():
    for exponent in reversed(range(140)):
        for numerator in range(64, 32, -1):
            yield Fraction(-numerator * 2**exponent, 32)
    for point in negative_half_grid():
        if point:
            yield point


def nodes(coeffs):
    # Choose a sample well inside each sign run to avoid near-root rounding.
    runs = []
    for x in grid():
        s = sign_at(coeffs, x)
        if s:
            if runs and runs[-1][0] == s:
                runs[-1][1].append(x)
            else:
                runs.append((s, [x]))
    assert len(runs) == len(coeffs) and runs[-1][0] == 1
    return [points[len(points)//2] for _, points in runs]


def main():
    path = Path('../../formal/LongCycleBounds/TwoCycle130RootData.lean')
    parts = ['import LongCycleBounds.TwoCycle130Arithmetic','import LongCycleBounds.DescentFiniteRoots','',
             'namespace LongCycleBounds.TwoCycle130RootData','open LongCycleFinite DescentNecklace TwoCycle130Arithmetic',
             'set_option maxRecDepth 100000','set_option maxHeartbeats 0']
    for label, row in zip(('lower','upper'), quotient_rows()):
        xs = nodes(row)
        dyadics = [f'⟨{x.numerator},{x.denominator.bit_length()-1}⟩' for x in xs]
        parts += ['', f'def {label}Nodes : Array LongCycleFinite.Dyadic := #[', ',\n'.join('  '+', '.join(dyadics[i:i+4]) for i in range(0,len(xs),4))+']',
                  f'private def {label}Values : List ℤ := [', ',\n'.join('  '+str(c) for c in row)+']',
                  f'private theorem {label}Values_eq : {label}Coeffs = {label}Values := by decide +kernel',
                  f'theorem {label}Mesh : negativeMeshOK {label}Coeffs {label}Nodes = true := by',
                  f'  rw [{label}Values_eq]', '  decide +kernel',
                  f'#print axioms {label}Mesh']
    parts += ['end LongCycleBounds.TwoCycle130RootData', '']
    path.write_text('\n'.join(parts))


if __name__ == '__main__':
    main()
