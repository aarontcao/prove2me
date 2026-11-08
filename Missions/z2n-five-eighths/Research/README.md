# Research record for z2n-five-eighths

This is the SAT computation behind the mission's `n = 7` data point, `f(7) = 80`. The UNSAT half still lacks a certificate, and `NEXT.md` says how to get one.

| file | what it holds |
|---|---|
| `REPORT.md` | the verdict and what moved |
| `claim-f7.md` | the claim, written for a hostile referee |
| `referee-f7-*.md` | one referee per joint: encoding, witness, UNSAT trust |
| `inherit.md` | what was taken from the Lean bench |
| `ledger.ndjson` | the append-only event record, with digests of every input |
| `instruments/cubefree.py` | the SAT and exhaustive-search instrument |
| `lib/numkit.py` | resource guards and the two-route validation helper |
| `tables/` | instrument output, including the two `n = 7` solver logs |
| `SOURCES.md` | the two papers the work relies on |

The Lean bench is our earlier Lean attempt at this problem, which isn't published.

The instrument needs `python-sat`. From this directory, `python3 instruments/cubefree.py --validate` checks that SAT and exhaustive search agree for `n = 1..4`. `python3 instruments/cubefree.py --decide 7 80` finds the witness, and `python3 -m pytest lib/ -q` runs the helper's tests.

The referee reports cite line numbers in the August 2026 draft of `instruments/cubefree.py`, so some no longer match the file.
