# What z2n-five-eighths inherits and does not re-derive

Parent bench: `z2n-five-eighths`. Run `leanck resume z2n-five-eighths` for its
own state.

## The question

Long and Wagner Conjecture 5.1, arXiv:1810.01225, open since October 2018. Let
`f(n)` be the largest cube-free subset of `Z_{2^n}`, where cube-free means no
`x, y, z` with all of `x`, `y`, `z`, `x+y`, `y+z`, `z+x`, `x+y+z` in the set.
The conjecture is `f(n) <= 5/8 * 2^n`.

## Sources read

| Source | Digest | What this campaign takes from it |
|---|---|---|
| bench `NEXT.md` | `8a960141d7c3` | Every reachable Lean node is closed. The `2/3` chain has no slack left. |
| bench `PROBLEM.md` | `eca7816b3190` | The exact `f(n)` values, and the prior-art position. |

## Will not re-derive

Each line below was established by the bench and cost real time. Re-deriving
any of them is waste, and the first two were themselves corrections of a wrong
belief held for part of a session.

1. The pair bounds leave `c1` free in `1..5`, so they never force `c1 = 1`, and
   `c0` ranges over `11..15`. An argument that assumes `c1 = 1` is wrong.
2. The odd-residue pigeonhole fails at two missing residues. Pigeonhole over
   the eight pairs `{u, u+16}` of odd residues fails once two odd residues are
   missing, so that route does not close `n = 5` and will not close anything
   larger.
3. The `2/3` chain cannot reach `5/8`, and the amount is exact. Its slack is
   the tail `2^(n-5) + 2^(n-7) + ...`, which is `2^n / 24`, and
   `2/3 - 5/8 = 1/24`. So the gap is a missing interaction between the layer
   pairs `(1,2)` and `(5,6)`, and sharpening a constant cannot supply it.
4. `upperBoundLayers` works by classification and never inducts on `n`. A
   union of layers is determined by the set `T` of 2-adic valuations it uses.
   Three distinct layers always build a cube, and so do two adjacent ones, so
   `T` holds at most two indices, at least two apart.
5. Every layer lemma in Section 4 of `Proof.lean` is `private`. An importing
   file cannot reach any of it.

## Prior art, inherited rather than re-checked

The `2/3` bound is **not new**. It is Theorem 3.1 plus the remark after it in
Yuchen Meng, arXiv:2311.12318, with a shorter proof than the bench's. The bench
found this only after the Lean work, which is the concrete local instance of
the "too strong to be new" risk.

A re-check of Semantic Scholar and OpenAlex on 2026-08-21 found three papers
citing Long and Wagner, none of which attacks Conjecture 5.1.

This campaign re-runs that check with `refsearch.py` rather than trusting the
inherited line, because the inherited check was manual and four days old at the
time this campaign opened.

## Known answers this campaign may use as controls

    f(1) = 1   f(2) = 2   f(3) = 5   f(4) = 10   f(5) = 20   f(6) = 40

All equal `2^(n-1) + 2^(n-3)`, that is exactly `5/8 * 2^n` for `n >= 3`. Each
was settled by SAT twice, under two independent encodings that agree, and every
optimum was re-verified cube-free by direct triple scan.

`f(7)` is **not settled**. SAT reached satisfiable at 80, and the run at 81 was
killed before it returned. `5/8 * 2^7 = 80`, so `f(7) = 80` if and only if 81
is unsatisfiable.
