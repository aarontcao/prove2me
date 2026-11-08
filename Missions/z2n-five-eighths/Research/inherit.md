# What z2n-five-eighths inherits and does not re-derive

This campaign started from an earlier Lean attempt on the same question, which we call the bench. The bench isn't published, so its `NEXT.md` and `PROBLEM.md` aren't in this repo. The digests below identify the versions we read. The question is Long and Wagner's Conjecture 5.1, arXiv:1810.01225: the largest cube-free subset of `Z_{2^n}` has size `f(n) <= 5/8 * 2^n`.

## Sources read

| Source | Digest | What this campaign takes from it |
|---|---|---|
| bench `NEXT.md` | `8a960141d7c3` | Every reachable Lean node is proved. The `2/3` chain can't be tightened to `5/8`. |
| bench `PROBLEM.md` | `eca7816b3190` | The exact `f(n)` values, and the prior-art position. |

## Will not re-derive

Items 1, 2, and 4 summarize the bench's findings, and this page doesn't reproduce the arguments behind them.

1. The bench's pair bounds don't force the tight configuration.
2. Pigeonhole over the eight pairs `{u, u+16}` of odd residues fails once two odd residues are missing. So it doesn't settle `n = 5` or anything larger.
3. The `2/3` chain can't reach `5/8`. Its slack is the tail `2^(n-5) + 2^(n-7) + ...`, which approaches `2^n / 24`, and `2/3 - 5/8 = 1/24`. So the gap is a missing interaction between the layer pairs `(1,2)` and `(5,6)`, not a constant to sharpen.
4. `upperBoundLayers` works by classification and never inducts on `n`. A union of layers is determined by the set of layers it uses. Three distinct layers always build a cube, and so do two adjacent ones. So it uses at most two layers, whose indices are at least two apart.

## Prior art

The `2/3` bound is **not new**. It's Theorem 9 and the remark after it in Yuchen Meng, *On Cube-Free Problems*, Electron. J. Combin. 2026 (Theorem 3.1 in arXiv:2311.12318). A check of Semantic Scholar and OpenAlex on 2026-08-21 found three papers citing Long and Wagner, none of which attacks Conjecture 5.1. This campaign re-ran that check with `refsearch.py`.

## Known answers this campaign may use as controls

    f(1) = 1   f(2) = 2   f(3) = 5   f(4) = 10   f(5) = 20   f(6) = 40

All equal `2^(n-1) + 2^(n-3)`, that is exactly `5/8 * 2^n` for `n >= 3`. The bench settled each by SAT under two independent encodings and re-verified every optimum cube-free by direct triple scan.

`f(7)` was **not settled**: SAT reached satisfiable at 80, and the run at 81 was killed before it returned.
