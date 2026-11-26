# Cycle selection and the real zeros of excedance polynomials

Two selection rules have identical one-cycle probabilities at n = 34 and 44. The independent selection row has n − 2 simple negative roots and a simple root at zero. The shared selection row has four nonreal roots, even though both conditional rows have simple real roots. At n = 44 every length from 2 to 43 has probability 1/2 and the full cycle has probability one. A second result concerns a deterministic profile with a unit tail beginning at 39. Its row at 39 has 37 simple negative roots and one simple zero, while its row at 40 has four nonreal roots.

Bowen Zuo, East China University of Science and Technology, takes responsibility for the paper. ChatGPT assisted in discovery, formalization, checking and drafting. This consolidated journal manuscript discloses both public preliminary reports and distinguishes the new same-marginal comparison and lower-row formal certificate. [Deterministic preprint](https://github.com/AlexZander-666/unrestricted-tail-excedance-counterexample/releases/tag/v1.0.0) · [Shared-profile preprint](https://github.com/AlexZander-666/excedance-cycle-profile-mixtures/releases/tag/v1.0.0)

Run the exact arithmetic and reproduce the PDF from this directory.

~~~sh
python3 -B certificates/independent_marginals.py
python3 -B reproduce.py
~~~

The certificate needs only the Python standard library. The build uses pdfLaTeX twice in each of two directories with TeX Live 2026, UTC, SOURCE_DATE_EPOCH=1795651200 and FORCE_SOURCE_DATE=1. The Lean project pins Mathlib and its dependencies to exact revisions. Prepare the cached dependencies and start a separate build with these commands. The fresh work directory must have an existing parent.

~~~sh
(cd formal && lake exe cache get)
python3 -Bu formal/verify_bounded.py formal DependenceAudit /tmp/dependence-clean-example --packages "$(realpath formal/.lake/packages)" --jobs 2
~~~

The final Lean theorem is LongCycleBounds.CycleProfile.joint_comparison. The theorems uniform44 and independent_cycle_assignments lie in the same namespace. The Lean result proves nonsplitting for the shared choices and the deterministic upper row. The exact counts of four nonreal roots use the rational Sturm certificates. See [proof](formal/LongCycleBounds/ProfileDependence.lean), [paper](main.pdf), and [reproduction script](certificates/independent_marginals.py).
