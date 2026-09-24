# Research record for z2n-five-eighths

This directory holds the numerical work behind the mission's `n = 7` data point. `REPORT.md`
opens with the verdict: `f(7) = 80`, reproduced with an independent SAT encoding and
a witness, and refereed on three joints. Two joints hold. The UNSAT half still lacks a
certificate, and `NEXT.md` says what would supply one.

| file | what it holds |
|---|---|
| `REPORT.md` | the verdict and what moved |
| `claim-f7.md` | the claim, written for a hostile referee |
| `referee-f7-*.md` | one referee per joint: encoding, witness, UNSAT trust |
| `notes.md`, `inherit.md` | running theory, and what was taken from the Lean bench |
| `ledger.ndjson` | the append-only event record, with digests of every input |
| `instruments/cubefree.py` | the SAT and exhaustive-search instrument |
| `lib/numkit.py` | resource guards and the two-route validation helper |
| `tables/` | instrument output, including the two `n = 7` solver logs |
| `SOURCES.md` | the two papers the work relies on |

The instrument needs `python-sat`. From this directory,
`python3 instruments/cubefree.py --validate` confirms that the SAT route and exhaustive
search agree for `n = 1..4`. `python3 instruments/cubefree.py --decide 7 80` finds the
witness. `python3 -m pytest lib/ -q` runs the helper's tests.

This work began in a separate private repository on 2026-08-25 and moved here on
2026-09-24.
