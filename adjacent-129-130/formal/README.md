# Adjacent binary-weighted rows with individual simple real roots

For the fixed binary cycle profile admitting all lengths at least 87, even lengths from 44 through 54, and even lengths from 76 through 86, the actual strict-excedance permutation rows of sizes 129 and 130 split over the reals. Both have a simple root at zero, and their respective sets of 127 and 128 negative roots are simple. Nevertheless the rows fail weak real interlacing. Every contributing permutation at either size has at most two cycles. Both sizes use exactly the same profile.

The result is `LongCycleBounds.TwoCycle130.individually_real_but_not_interlacing`. This version adds independent individual-root certificates to the separately frozen pairwise failure. [Statement map](STATEMENT-MAP.md)

## Verify the proofs

Install elan, Git and Python 3. From the extracted source ZIP run the following commands.

```sh
sha256sum -c SHA256SUMS
python3 -B certificates/replay_roots.py
LEAN_NUM_THREADS=1 python3 -Bu verify_lean.py . TwoCycle130RootsAudit --jobs 2
```

The first Python verifier recomputes the two coefficient lists and four signs, reproduces the frozen dyadic bracket data and an independent reciprocal-grid calculation, and regenerates the Lean mesh source in a temporary tree for an exact byte comparison. The source-cold Lean verifier builds the actual original-input proof from an empty local project, checks its 18 named declarations, and replays the project modules separately in the kernel. Supply `--packages /path/to/.lake/packages` to reuse the pinned dependency checkouts and cache. The arithmetic and exact mesh modules benefit from generous RAM on machines with the full Mathlib cache.
