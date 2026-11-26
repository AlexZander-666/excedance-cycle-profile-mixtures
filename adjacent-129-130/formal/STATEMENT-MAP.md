# Definition, scope and proof map

| Mathematical step | Lean implementation |
| --- | --- |
| Original strict excedance counts and actual product of cycle weights | [`LongCycles.excedances`](LongCycles/Statement.lean), [`CycleProfile.row`](LongCycleBounds/CycleProfile.lean) |
| One common binary profile and unit tail from length 87 | [`TwoCycle130.keep`, `weight`, `unit`, `unit_tail`](LongCycleBounds/TwoCycle130Rows.lean) |
| At most two cycles whenever a permutation of size at most 130 has all cycle lengths retained | [`TwoCycle130.at_most_two`](LongCycleBounds/TwoCycle130Rows.lean) |
| True rows factor as $tP$ and $tQ$ | [`TwoCycle130.lower_row` and `upper_row`](LongCycleBounds/TwoCycle130Rows.lean) |
| Coefficient lists compute the two true quotient formulas | [`TwoCycle130Arithmetic.lowerCoeffs_spec` and `upperCoeffs_spec`](LongCycleBounds/TwoCycle130Arithmetic.lean) |
| At the rational point, $P<0$, $Q>0$, $P'>0$ and $Q'>0$ | [`TwoCycle130Arithmetic.evaluated_signs`](LongCycleBounds/TwoCycle130Arithmetic.lean) |
| Failure of weak real interlacing of the actual nondivided rows | [`TwoCycle130.original_not_interlacing`](LongCycleBounds/TwoCycle130Verified.lean) |

The predecessor admits only the full 129-cycle type. For 130 letters the shorter length of a two-cycle term belongs to `{44,46,48,50,52,54}`, and the other length is its complement to 130. Distinct shorter and longer lengths make the number of unordered supports exactly the binomial coefficient `choose(130,a)`.

An independent [exact rational script](certificates/check_arithmetic.py) computes the Eulerian coefficients from the alternating binomial formula and verifies the four displayed signs. The Lean verifier computes the coefficients via the existing Eulerian recurrence and checks integer Horner values and derivatives with the kernel. The conclusion is a pairwise obstruction. The additional individual splitting in this version is verified below.

## Individual splitting and multiplicities

The [augmented top-level theorem](LongCycleBounds/TwoCycle130SeparateRoots.lean) proves the two `SimpleRow` properties and the pairwise obstruction together. Each `SimpleRow` gives complete splitting, a duplicate-free root multiset containing zero, and complete counts of negative and total roots. It applies directly to the actual nondivided permutation rows. The new proof checks separate full-axis dyadic meshes in [TwoCycle130RootData.lean](LongCycleBounds/TwoCycle130RootData.lean). Each mesh certifies its own quotient's degree-many distinct negative roots through `negativeMeshOK_sound`, without assuming that either row interlaces the other.

The independent small-axis checks use dyadic integer signs in (−1,0), reciprocal symmetry, and the central root at −1 of the odd-degree quotient. They give the same separate root counts. These checks and the Lean full-axis checks share the exact quotient formulas and use separate isolation calculations.
