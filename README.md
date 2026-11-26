# Nonreal averages of real-rooted cycle-restricted excedance polynomials

On 44 letters two polynomials, each with 42 simple negative zeros and a simple zero at the origin, have an arithmetic mean with nonreal zeros. Both count permutations by strict excedances and allow the full 44-cycle. A second example on 34 letters has mixing weights one third and two thirds. [Paper](paper/main.pdf) · [Joint Lean theorem](formal/LongCycleBounds/MixedProfilesVerified.lean)

For a set of allowed cycle lengths S, an endpoint counts each permutation of n letters whose cycle lengths belong to S with the monomial t raised to the number of indices i for which π(i)>i. Each set contains every length j≥n and excludes 1. The permitted smaller lengths are as follows.

| n | First endpoint | Second endpoint |
|---|---|---|
| 34 | 3,4,7,10,13,14,16,17,20,23 | 2,3,5,6,8,9,12,15,18,21,24,27 |
| 44 | 2,4,6,9,11,13,16,18,20,23,25,27,30,32,34,36,37,39,41,43 | All integers from 2 through 43 outside the first list |

For the mixture of whole polynomials take f = A+2B at size 34 or f = A+B at size 44. The exact difference f′²−ff″ is negative at −2/15 or −1/2, respectively. The normalized mixtures divide these differences by 9 or 4. The supplied Python checker computes each coefficient by two independent methods and checks all endpoint signs with integers. Rational Sturm chains leave four nonreal zeros for each mixture. Lean starts from the weighted sum over actual permutations, proves the exact endpoint multiplicities, and shows that each mixture fails to split over the reals. [Exact replay](verification/integer-replay.log) · [Axiom inventory](verification/axioms.txt)

Alexandersson’s public conjecture varies the size while holding a hard minimum cycle length fixed. The counterexamples here concern a fixed-size convex compatibility extension. A prior size-12 positive sum already implies a nonreal equal-weight average for two real-rooted conjugacy-class polynomials. Those endpoints omit the full cycle and have a multiple zero. [Original problem](https://www.symmetricfunctions.com/realRootedOpenProblems.htm#permutations-with-long-cycles) · [Prior work](PRIOR-ART.md)

## Reproduce

The integer and rational certificate uses Python 3 with its standard library. The printed proof checker also needs pdfLaTeX. The formal source requires Lean 4.33.1, the Lake dependencies at the nine pinned commits, and enough disk space for Mathlib. From the research archive run

~~~sh
python3 -IBu certificates/original_rows.py
python3 -IBu paper/reproduce.py
python3 formal/verify_lean.py formal MixedProfilesAudit --serial
~~~

The last command builds and independently kernel-replays 99 non-audit modules and then runs the audit source directly. To reproduce the receipt for all 100 modules (including a separate build and kernel replay of MixedProfilesAudit), first prepare the external packages with the project's lock and choose an unused local directory. From the extracted archive run

~~~sh
(cd formal && lake exe cache get)
python3 formal/verify_bounded.py formal MixedProfilesAudit ./fresh-mixed-profiles-build --packages formal/.lake/packages --jobs 1
~~~

The work directory must be new. This driver verifies the dependency revisions, starts with no project proof objects, checks every module in the original import closure, and checks the 12 axiom reports. The same closure and theorem names were used in the supplied bounded-parallel receipt.

Bowen Zuo, East China University of Science and Technology, is the sole author and takes responsibility for the paper. Version 1.0.0 candidate, 26 November 2026. ChatGPT assisted with discovery, formalization, verification and drafting.
