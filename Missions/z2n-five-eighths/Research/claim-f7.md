# Claim: `f(7) = 80`

Standalone. Written for a hostile referee. Do not read `REPORT.md`, `notes.md`
or the ledger; everything needed is here.

## Definitions

Work in `Z_N` with `N = 2^n`. A set `A` contained in `Z_N` is **cube-free** when
there is no triple `(x, y, z)` of elements of `Z_N` with all seven of

    x,  y,  z,  x+y,  y+z,  z+x,  x+y+z

lying in `A`. The triple ranges over all of `Z_N`, not over `A`, and degenerate
choices such as `x = y = z` are allowed. `f(n)` is the largest cardinality of a
cube-free subset of `Z_{2^n}`.

This is the quantity in Conjecture 5.1 of Jason Long and Adam Zsolt Wagner,
"The largest projective cube-free subsets of `Z_{2^n}`", arXiv:1810.01225. The
conjecture is `f(n) <= 5/8 * 2^n` for all `n`. It is open.

## The claim

    f(7) = 80,   and   5/8 * 2^7 = 80.

So Conjecture 5.1 holds with equality at `n = 7`.

## Status of this value before the claim

Known exactly: `f(1..6) = 1, 2, 5, 10, 20, 40`. Each equals `2^(n-1) + 2^(n-3)`,
which is `5/8 * 2^n` for `n >= 3`.

`f(7)` was **not** settled on this machine. A prior run reached satisfiable at
80 under a different script and was killed at 81 before it returned a verdict.

## The argument

It is a finite computation, so the argument is entirely about whether the
computation computes what it claims to.

### Step 1: residue 0 is excluded without loss

Take `x = y = z = 0`. The seven
elements are all `0`. So any set containing `0` contains a cube, and every
cube-free set omits `0`. The encoding therefore fixes the variable for residue
`0` to false. This restriction on the search space keeps every cube-free set.

### Step 2: the encoding of cube-freeness

One Boolean variable per residue, variable `v+1` for
residue `v`. For every cube `C`, taken as the *set*
`{x, y, z, x+y, y+z, z+x, x+y+z}` of its seven expressions, add the clause

    NOT v_c1  OR  NOT v_c2  OR  ...

over the distinct elements of `C`. A satisfying assignment therefore selects a
set meeting no cube in all of its elements, which is exactly cube-freeness.
Degenerate triples collapse `C` to fewer than seven distinct elements and are
kept, since they are the strongest constraints.

### Step 3: the cardinality constraint

A sequential-counter encoding
(`pysat` `CardEnc.atleast`, `EncType.seqcounter`) over the 127 variables for
residues `1..N-1`, with bound `t`. So the formula is satisfiable exactly when a
cube-free set of size at least `t` exists.

### Step 4: the two solver runs

Cadical195, single thread, 10 GB address-space cap.

    decide(7, 81)  ->  UNSAT   (27 minutes)
    decide(7, 80)  ->  SAT     with a witness

### Step 5: the two runs give `f(7) = 80`

SAT at 80 gives `f(7) >= 80`. UNSAT at 81 gives
`f(7) <= 80`. Hence `f(7) = 80`.

## The witness, written out

    A = { v in Z_128 : v mod 8 is one of 1, 3, 4, 5, 7 }

Five residue classes mod 8, each of size 16, so `|A| = 80`. In layer language
this is the odd layer, of size `2^(n-1) = 64`, together with the four-times-odd
layer, of size `2^(n-3) = 16`.

This is Long and Wagner's own extremal construction. The solver was not told
it and reached it anyway.

## Prior art: novelty is NOT claimed

Long and Wagner, Section 5, p. 21, verbatim: "Using Gurobi [12] we could check
that for `n <= 7` the following stronger conjecture is also true." Their
Conjecture 5.2 at `n = 7` implies `f(7) <= 80`, and their construction supplies
the matching lower bound. So **the value `f(7) = 80` follows from what they
already report, and is not new.**

The number 80 never appears in the paper. Long and Wagner do not supply a table
of exact `f(n)`, a model, code, or a certificate. No other work computes exact
values either. Three distinct papers cite them, and none computes `f(n)`. The
OEIS lacks an entry for the sequence.

So the only thing on offer here is a **reproduction from an independent
encoding and an independent solver, with the witness written down**. That is
worth having and it is a small thing. Anyone reading this claim as new
mathematics has misread it.

## Why the instrument should be believed

The same code, unchanged, was run on the six cases whose answers are already
known.

- For every `n` in `1..6` it returned SAT at `f(n)` **and** UNSAT at `f(n)+1`.
  So both the SAT side and the UNSAT side are exercised on six known values.
- Every SAT witness was re-checked cube-free by `is_cube_free`, which tests the
  definition directly by scanning triples and never calls the cube enumerator
  the encoding uses.
- On `n` in `1..4`, where a second route is feasible, exhaustive search over all
  subsets agrees with SAT exactly.
- A planted-set test: a set built to be cube-free by construction is classified
  cube-free, the full group is classified not cube-free, and SAT recovers the
  planted size.

## The three joints

A referee is dispatched at exactly one of these.

- The `encoding` joint asks whether Steps 1 to 3 faithfully express "a cube-free
  set of size at least `t`". It includes the 0-exclusion, the clause
  construction over `cubes(n)`, and the cardinality constraint. The specific
  worry: `cubes(n)` generating too few cubes would make the formula too weak, so
  UNSAT at 81 would be claiming more than the mathematics supports.

- The `unsat_trust` joint asks whether the UNSAT answer at 81 may be believed.
  No DRAT proof certificate was produced or checked. A solver bug, a memory-cap
  interaction, or a silently truncated formula would all present as UNSAT. The
  specific worry: the SAT direction has a witness that is independently
  re-verified, and the UNSAT direction has nothing analogous.

- The `witness` joint asks whether SAT at 80 really exhibits a cube-free set of
  size 80. It includes whether `is_cube_free` tests the stated definition, and
  whether the reported size counts what it should. The specific worry:
  `is_cube_free` iterates `x, y, z` over the set `A` rather than over `Z_N`, so
  it could be checking a weaker condition than the definition above states.

## What is not claimed

The range `n >= 8` and the conjecture in general lie outside the claim. A single
verified value is not evidence of a pattern beyond the range checked, and
`f(1..7)` all matching `2^(n-1) + 2^(n-3)` is consistent with the conjecture
failing at some larger `n`.

Not novelty. See the prior-art section above.

Not an audited UNSAT. The `f(7) <= 80` half rests on a solver run lacking a
proof certificate, and that is the weakest point in this claim. Long and
Wagner's Gurobi check agrees, which makes the mathematics likelier and audits
our run not at all. Two unaudited computations agreeing is still two unaudited
computations.
