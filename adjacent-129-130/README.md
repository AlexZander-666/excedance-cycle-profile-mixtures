# Two real-rooted adjacent rows that fail to interlace

Take every length at least 87 and the twelve lengths 44, 46, 48, 50, 52, 54, 76, 78, 80, 82, 84, 86. For each permitted permutation, count indices where its value exceeds its index. At sizes 129 and 130 the resulting rows have 127 and 128 simple negative roots, respectively, together with a simple zero. They fail weak interlacing.

Writing the rows as $tP$ and $tQ$, the four signs at $t=-1/9800000000000000$ are $P<0$, $P'>0$, $Q>0$, and $Q'>0$. Hence $Q'P-QP'<0$ there. For weakly interlacing monic polynomials with these degrees, partial fractions give $Q'P-QP'>0$ away from the roots of $P$. Only the full 129-cycle contributes to the lower row. The upper row contains a full cycle and six types with two cycles. [Proof and construction, Theorem 3.1](paper/main.pdf) · [Independent dyadic certificates](certificates/ordered-brackets.tsv)

The length rule stays fixed as the size increases. Alexandersson's question uses a hard minimum, under which every length above the minimum is retained. Earlier work exhibits a different obstruction at fixed size eight when the cutoff changes from four to five. [Original question](https://www.symmetricfunctions.com/realRootedOpenProblems.htm#permutations-with-long-cycles) · [Earlier fixed-size calculation](https://github.com/1337isnot1337/solved-conjectures/blob/0c07434ef991b853528ca55926b3b83820b7f58d/docs/alexandersson-long-cycle-research.md#boundary-cross-threshold-interlacing-is-false)

## Reproduce from this directory

```sh
python3 -B certificates/verify_130.py
python3 -B formal/certificates/replay_roots.py
(cd formal && sha256sum -c SHA256SUMS)
LEAN_NUM_THREADS=1 python3 -Bu formal/verify_lean.py formal TwoCycle130RootsAudit --jobs 2
python3 -B paper/reproduce.py
```

The Python checks use integer arithmetic. The paper rebuild needs PDFLaTeX, the cite, titlesec, caption, lmodern and microtype packages, and TeX Live 2026 for the reference PDF. The Lean verifier uses the locked dependencies and the supplied toolchain. [Lean toolchain](formal/lean-toolchain) · [Mathlib lock](formal/lake-manifest.json) · [Proof entry](formal/LongCycleBounds/TwoCycle130SeparateRoots.lean)

A source-cold DGX Spark build replayed 102 project modules and audited 18 declarations. The combined Lean theorem starts with the actual permutation enumerators and proves the separate root counts and failure of weak interlacing. The fifth/sixth root order is supplied by the independent ordered brackets. The independent alternating-binomial implementation linked in the frozen formal statement map is at [check_arithmetic.py](formal/certificates/two-cycle-130/check_arithmetic.py). [Audit by declaration](verification/lean-receipt.json) · [Kernel replay](verification/kernel-replay.txt)

Bowen Zuo, East China University of Science and Technology. Version 1.2.0, 26 November 2026. ChatGPT assisted in discovery, formalization, checking and drafting. The author takes responsibility for this release. For the journal manuscript see the authorship note in the [top-level README](../README.md#authorship). The original software follows the repository license and the paper has separate terms. [Rights](../LICENSE-SCOPE.md)
