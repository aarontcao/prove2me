VERDICT: PARTIAL f(7) = 80 reproduced and refereed, two joints hold, and the UNSAT half is uncertified

# z2n-five-eighths

Let `f(n)` be the size of the largest cube-free subset of `Z_{2^n}`. Long and Wagner's Conjecture 5.1 (arXiv:1810.01225, October 2018) says `f(n) <= 5/8 * 2^n`.

## What moved

- We reproduced `f(7) = 80`, which the bench had left open, but the UNSAT half lacks a certificate. `decide(7, 81)` returns UNSAT, and `decide(7, 80)` returns SAT with an 80-element witness re-verified cube-free. So, pending that certificate, Conjecture 5.1 holds with equality at `n = 7`. The value itself isn't new, since the Gurobi check Long and Wagner report for `n <= 7` implies it. We add a reproduction with an independent encoding and solver, plus the witness written down.
- The extremal set is `A = {v : v mod 8 in {1,3,4,5,7}}`, five classes of 16. That's Long and Wagner's own construction, which the solver wasn't told.
- Meng, *On Cube-Free Problems*, Electron. J. Combin. 33(1) 2026 #P1.16, the newest paper citing Long and Wagner, still calls `(5/8 + o(1))N` a conjecture. Nobody has published exact values of `f(n)`, and Long and Wagner omit a table of them. OEIS A084215 lists the same terms, as the expansion of $(1+x^2)/(1-2x)$, but doesn't mention cube-free sets.

## What is ruled out

- The `2/3` bound isn't a contribution. Meng 2026 calls it "quite trivial" and proves it for every cyclic group, not just `Z_{2^n}`.
- Meng's Conjecture 4 doesn't reach this problem. It bounds `d`-cube-free subsets of `Z_N` by `(d-1)N/d` and requires `d | N`, but here `d = 3` and `N = 2^n`.
- We don't reopen three dead ends from the bench. The pair bounds don't force `c1 = 1`, and the odd-residue pigeonhole over `{u, u+16}` fails once two odd residues are missing. The `2/3` chain's slack is exactly `2^n/24`, and `2/3 - 5/8` is 1/24. So the gap is a missing interaction between layer pairs `(1,2)` and `(5,6)`, not a constant to sharpen.
- `f(7) = 80` isn't a contribution on its own, since Long and Wagner's Gurobi check implies it. What they don't supply is a certificate.
- Our UNSAT at 81 isn't auditable: the log lacks a conflict count, clause count, hash, or DRAT certificate. Gurobi agreeing makes the mathematics likelier but doesn't audit our run.

## Numbers

Every figure below except the greedy row comes from `instruments/cubefree.py`, which has a passing `validate` and a passing `plant` event in the ledger. The greedy row comes from the `encoding` referee's own run (ledger entry 29).

| Quantity | Value | How |
|---|---|---|
| `f(1..4)` | 1, 2, 5, 10 | Two independent routes, SAT and exhaustive search, residual 0 |
| `f(1..6)` | 1, 2, 5, 10, 20, 40 | SAT, every witness re-verified cube-free by direct triple scan |
| `f(n)` for `3 <= n <= 6` | `2^(n-1) + 2^(n-3)` | Exactly `5/8 * 2^n` |
| `f(7)` | **80** | SAT at 80 with a verified witness; UNSAT at 81 in 27 minutes |
| the `n=7` extremal set | `{v : v mod 8 in {1,3,4,5,7}}` | Read off the SAT model, independently re-verified cube-free with no solver |
| greedy maximal sets at `n=7` | max 56, mean 36.7 over 400 runs | Randomized greedy, so `80` is far above what the random landscape reaches |

Both controls pass. `decide_sat(n, f(n))` is satisfiable at `n = 4, 5, 6` with every witness re-verified, so the pipeline doesn't certify a bound below the truth. And `2^(n-1) + 2^(n-3)` fitted on `f(1..5)` predicts `f(6) = 40`. We held out `f(6)` because a fit on all six values would confirm `5/8` trivially.

## Referees on claim f7

Three joints, one blind referee each.

| Joint | Verdict | What it established |
|---|---|---|
| `encoding` | HOLDS | `cubes(n)` is set-equal to a from-scratch re-enumeration at `n = 1..5` and `n = 7`, counts `2, 9, 78, 668, 5448, 349968`. Exhaustive ground truth over all subsets at `n = 1..4` for every `t`. The seqcounter projects exactly to `popcount >= t`, checked exhaustively at `n = 3, 4`. 31191 size-`>=81` assignments across two runs, zero disagreements with a direct triple scan. The referee file reports the first run alone, 25191 assignments, and the ledger adds the second. Five different cardinality encodings under reversed variable numbering all give `f(1..6)`. |
| `witness` | HOLDS | Reproduced `n = 7` from scratch: SAT, exactly 80 elements, cube-free against the literal definition with `x, y, z` over all of `Z_128`. Found the closed form and a third route with no solver at all. |
| `unsat_trust` | **UNCLEAR** | Ruled out every mechanical failure it could test: the cardinality encoding is not vacuous at the exact `n = 7` parameters, the memory cap aborts rather than reporting UNSAT, and there is no signal path turning UNKNOWN into UNSAT. But the run itself is unauditable. |

Both HOLDS verdicts rest on independent re-implementations. The referees also found two defects, now fixed. `--decide` hardcoded `ok: True` whether or not the witness passed the cube-free scan, and the claim never printed the witness.

## Red team

Worst first.

1. The UNSAT at 81 is uncertified, and `f(7) <= 80` rests on nothing else. `pysat` can emit DRAT, but we didn't have a checker installed.
2. The prior-art sweep could have missed a paper that solves this without citing Long and Wagner. The citation graph holds only three citing papers.
3. `f_sat` and `f_brute` share `cubes()`. The `encoding` referee re-enumerated `cubes(n)` from scratch, and the `witness` referee's third route touches neither `cubes()` nor `is_cube_free`.
4. The hold-out control is weak. The pattern `2^(n-1) + 2^(n-3)` was known before the fit, so it tests arithmetic more than the instrument.

Only item 1 can make `f(7) = 80` wrong as a statement about our computation, and it's why the verdict is PARTIAL. It's not a worry about the mathematics, since Long and Wagner's Gurobi check agrees.

## Tooling

The campaign gates caught two real defects. `campaign instrument` refused the first `--known` run because `CardEnc.atleast` raised at `n = 1`, where the bound exceeds the literal count, and recorded `ok:false`. `campaign close` refused a PROVEN verdict that disagreed with `REPORT.md`.
