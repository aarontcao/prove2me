# Next action for z2n-five-eighths

Derived, and rewritten freely. Exactly one action, as a literal command line.

next: ask the human whether to install a DRAT checker, then certify the f(7) UNSAT

why: `f(7) = 80` is established and refereed, and the one joint that came back
UNCLEAR is the only thing keeping the verdict at PARTIAL. The `unsat_trust`
referee ruled out every mechanical failure it could test and then said the run
itself is unauditable: `tables/sat-n7-81.log` is 234 bytes without a conflict
count, a clause count, or a proof. Long and Wagner's Gurobi check agrees,
which makes the mathematics likelier and audits our run not at all.

`pysat` can already emit DRAT: `Cadical195(..., with_proof=True)` plus
`get_proof()`. The pipeline still needs a checker. `drat-trim` is not in Debian 12 apt,
so it means either building it from source or installing `cadical` and
`cryptominisat`, which are in apt. Both change machine state, so ask first.

Expect the certificate to be large and the check to take longer than the
27-minute solve. Run it as a detached background job, not inline, and validate
the whole pipeline at `n = 6, t = 41` first, where UNSAT is known and takes
seconds.

## After that

The real gap is untouched: the `2/3` chain's slack is exactly `2^n/24`, and
closing it needs an interaction between layer pairs `(1,2)` and `(5,6)`.

There is now a concrete handle on it. Every extremal set found so far, at
`n = 4` and `n = 7`, is `{v : v mod 8 in {1,3,4,5,7}}`, the preimage of a
cube-free set in `Z_8`. If that holds at every `n`, the whole question reduces
to `Z_8` and the `5/8` constant is just `|T|/8` for `T = {1,3,4,5,7}`. Test it:
have the instrument return several distinct extremal sets at `n = 5` and
`n = 6` and check whether all of them are pulled back from `Z_8`. If some are
not, that is the more interesting answer.

## Do not

Do not re-derive the three inherited dead ends in `inherit.md`. Do not treat
`f(7) = 80` as new: Long and Wagner's Gurobi check already implies it, and this
is recorded as prior-art Tier 3. Do not treat the `2/3` bound as a
contribution: Meng 2026 calls it trivial. Do not raise the verdict above
PARTIAL while `unsat_trust` is UNCLEAR.
