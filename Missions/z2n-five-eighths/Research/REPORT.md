VERDICT: PARTIAL f(7) = 80 reproduced and refereed, two joints hold, and the UNSAT half is uncertified

<!--
Assembled by `leanck campaign report z2n-five-eighths`. Verdict first, because a
reader who stops after one line must still get the answer.
-->

# z2n-five-eighths

Long and Wagner Conjecture 5.1, arXiv:1810.01225. Let `f(n)` be the largest
projective-cube-free subset of `Z_{2^n}`. The conjecture is
`f(n) <= 5/8 * 2^n`. Open since October 2018.

This campaign is also the acceptance test for the campaign layer itself, so
read it as two results: what it learned about the problem, and whether the
tooling worked.

## What moved

<!-- Up to three bullets. What is true now that was not true before. -->

- `f(7) = 80`, which the bench recorded as unsettled after a run that was
  killed. `decide(7, 81)` is UNSAT in 27 minutes and `decide(7, 80)` is SAT in
  under two, with a witness of exactly 80 elements re-verified cube-free. So
  Conjecture 5.1 holds with equality at `n = 7`. **This value is not new**: it
  follows from the Gurobi check Long and Wagner already report for `n <= 7`.
  What is new here is a reproduction with an independent encoding, an
  independent solver, and the witness written down.
- The extremal set has a closed form and it is the published one.
  `A = {v : v mod 8 in {1,3,4,5,7}}`, five classes of 16. The solver reached
  Long and Wagner's own construction without being told it. The same `mod 8`
  structure appears at `n = 4`.
- The prior-art position is settled in both directions. Meng, `On Cube-Free
  Problems`, Electron. J. Combin. 33(1) 2026 #P1.16, is the newest paper citing
  Long and Wagner and it names `(5/8 + o(1))N` as still conjectured. So the
  target is open as of a 2026 journal paper. Nobody has published exact `f(n)`
  for `n >= 7`, the sequence is absent from OEIS, and Long and Wagner omit a
  table of exact values.
- The SAT pipeline is repaired and validated. It was dead on this box: three
  committed scripts under the bench's `search/` imported `pysat`, which was not
  installed anywhere.

## What is ruled out

<!--
The section that pays. A negative result a later session inherits is worth more
than a positive one it cannot reproduce.
-->

- The `2/3` bound is not a contribution, and now demonstrably so. Meng 2026
  calls it "quite trivial" and gives it in one paragraph for every cyclic
  group, not just `Z_{2^n}`. The bench already knew the 2023 version of this.
  The 2026 paper closes the question.
- Meng's Conjecture 4 does not reach this problem. It bounds `d`-cube-free
  subsets of `Z_N` by `(d-1)N/d` and requires `d | N`. Here `d = 3` and
  `N = 2^n`, and 3 never divides `2^n`. Theorem 5(iii), the prime-power case,
  is a case of Conjecture 4 and so inherits `d | N`. It does not apply.
- Three inherited dead ends stay dead, and are not re-derived here: the
  pair bounds do not force `c1 = 1`; the odd-residue pigeonhole over
  `{u, u+16}` fails once two odd residues are missing; and the `2/3`
  chain's slack is exactly `2^n/24`, which equals `2/3 - 5/8`, so the gap is a
  missing interaction between layer pairs `(1,2)` and `(5,6)` and not a
  constant to be sharpened.
- `f(7) = 80` is not a contribution on its own. It follows from Long and
  Wagner's reported Gurobi check for `n <= 7`. Anyone reporting it as new has
  misread the source. Recorded as Tier 3: continue on what they disclaim, which is the
  certificate and not the value.
- Our UNSAT at 81 is not auditable, and no amount of external agreement fixes
  that. The log runs to 234 bytes without a conflict count, clause count, hash,
  or DRAT certificate. Gurobi agreeing makes the mathematics likelier and
  audits our run not at all. Two unaudited computations agreeing is still two
  unaudited computations.

## Numbers

Every figure below comes from `instruments/cubefree.py`, which has a passing
`validate` and a passing `plant` event in the ledger.

| Quantity | Value | How |
|---|---|---|
| `f(1..4)` | 1, 2, 5, 10 | Two independent routes, SAT and exhaustive search, residual 0 |
| `f(1..6)` | 1, 2, 5, 10, 20, 40 | SAT, every witness re-verified cube-free by direct triple scan |
| `f(n)` for `3 <= n <= 6` | `2^(n-1) + 2^(n-3)` | Exactly `5/8 * 2^n` |
| `f(7)` | **80** | SAT at 80 with a verified witness; UNSAT at 81 in 27 minutes |
| the `n=7` extremal set | `{v : v mod 8 in {1,3,4,5,7}}` | Read off the SAT model, independently re-verified cube-free with no solver |
| greedy maximal sets at `n=7` | max 56, mean 36.7 over 400 runs | Randomized greedy, so `80` is far above what the random landscape reaches |

Controls, both passing:

- Over-certification: `decide_sat(n, f(n))` is satisfiable at `n = 4, 5, 6`
  and every witness re-verifies. The pipeline does not certify a bound below
  the truth, so a future UNSAT from it means something.
- Hold-out: fitting `2^(n-1) + 2^(n-3)` on `f(1..5)` predicts `f(6) = 40`,
  which is correct. This matters because `f(1..6)` is exactly `5/8 * 2^n`, so
  an instrument fitted on all of it would confirm `5/8` trivially.

## Referees on claim f7

Three joints, three blind referees, one each.

| Joint | Verdict | What it established |
|---|---|---|
| `encoding` | HOLDS | `cubes(n)` is set-equal to a from-scratch re-enumeration at `n = 1..5` and `n = 7`, counts `2, 9, 78, 668, 5448, 349968`. Exhaustive ground truth over all subsets at `n = 1..4` for every `t`. The seqcounter projects exactly to `popcount >= t`, checked exhaustively at `n = 3, 4`. 31191 size-`>=81` assignments across two runs, zero disagreements with a direct triple scan. The referee file reports the first run alone, 25191 assignments, and the ledger adds the second. Five different cardinality encodings under reversed variable numbering all give `f(1..6)`. |
| `witness` | HOLDS | Reproduced `n = 7` from scratch: SAT, exactly 80 elements, cube-free against the literal definition with `x, y, z` over all of `Z_128`. Found the closed form and a third route with no solver at all. |
| `unsat_trust` | **UNCLEAR** | Ruled out every mechanical failure it could test: the cardinality encoding is not vacuous at the exact `n = 7` parameters, the memory cap aborts rather than reporting UNSAT, and there is no signal path turning UNKNOWN into UNSAT. But the run itself is unauditable. |

The two HOLDS verdicts came with independent re-implementations, not with
agreement. Both referees also found real defects, now fixed: `--decide`
hardcoded `ok: True` regardless of whether the witness passed the cube-free
scan, and the claim never printed the witness.

## Red team

<!-- Ranked by my own worry, worst first. -->

1. The UNSAT at 81 is uncertified, and the bound `f(7) <= 80` rests on nothing
   else. The log does not have a conflict count, a clause count, or a DRAT
   proof, so the run cannot be checked after the fact. `pysat` can emit DRAT,
   but no checker is installed on this box.
2. The prior-art sweep could still have missed something. The citation graph
   holds only three citing papers. A paper solving this without citing Long
   and Wagner would be invisible to `--cited-by`.
3. The two routes are less independent than the word suggests. `f_sat` and
   `f_brute` share `cubes()`. Now largely covered: the `encoding` referee
   re-enumerated `cubes(n)` from scratch and got set equality at `n = 1..5` and
   `n = 7`, and the `witness` referee's third route touches neither `cubes()`
   nor `is_cube_free`.
4. The hold-out control is weak. The pattern `2^(n-1) + 2^(n-3)` was known
   before the fit, so predicting `f(6)` from `f(1..5)` tests arithmetic more
   than it tests the instrument.

At stake: only item 1 can make `f(7) = 80` wrong as a statement about our own
computation, and it is the reason the verdict is PARTIAL rather than PROVEN.
Item 2 bounds novelty, which is already claimed as nil. Items 3 and 4 were the
top worries before refereeing and are now largely closed. Note that item 1 is
not a worry about the mathematics: Long and Wagner's independent Gurobi check
agrees, so `f(7) = 80` is very probably true. It is a worry about whether *this
run* is evidence for it.

## Tooling verdict

The layer worked, and it caught two real defects rather than waving
them through.

- `campaign instrument` refused the first `--known` run because `CardEnc.atleast`
  raised at `n = 1`, where the bound exceeds the literal count. It recorded
  `ok:false` and said the output could not be cited. That is the gate working.
- `campaign close` refused a `PARTIAL` verdict without a control, refused an
  experiment citing an unvalidated instrument, and refused a verdict that
  disagreed with `REPORT.md`.
- `campaign note ... referee --joint bogus` refused a joint the claim had not
  declared.
- The killtest's own first campaign run resolved no pgid, fell back to `0`, and
  `kill -9 -0` killed the test's own process group. That is exactly the
  accident `campaign run` exists to prevent, and the test now refuses to signal
  a group it cannot name.

No claim was formed, so no referee was dispatched against this campaign's
mathematics. The referee path was exercised against a deliberately false
fixture instead, and it broke it correctly.
