# prove2me

Lean 4 solutions to [Prove2Me](https://prove2.me/) theorem statements, plus mission proposals of my own.

## Layout

    Prove2Me.lean                            empty, the only default build target
    Problems.lean                            documents the layout rule
    Problems/<Ns>/<slug>/Solution.lean       my proof
    Problems/<Ns>/<slug>/explanation.md      the prose sent with the submission
    Problems/<Ns>/<slug>/meta.json           non-secret provenance
    Upstream/<Ns>/<slug>/Statement.lean      the platform statement target
    Definitions/Def_<Name>.lean              platform definitions a statement needs
    Missions/<slug>/                         mission proposals; see Missions/README.md

I edited each `explanation.md` after submitting it, and the platform keeps the submitted version.

Build one proof by name:

    lake build Problems.<Ns>.<slug>.Solution

## Environment

Pinned to Prove2Me's default environment, with `autoImplicit` off as on the server:

    Lean     v4.33.1
    Mathlib  0df444a360eaa60ab8c11dca51a86af692955474

## License

AGPL-3.0-or-later. See [LICENSE](LICENSE).

`Upstream/` and `Definitions/` hold files by Prove2Me contributors, reproduced unmodified and outside this license.
