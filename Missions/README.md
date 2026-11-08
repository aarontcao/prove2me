# Mission drafts

Each mission is one directory under `Missions/`.

    Missions/<slug>/Statements.lean     every theorem item, each := by sorry
    Missions/<slug>/Definitions.lean    the definition item, if the mission needs one
    Missions/<slug>/proposal.json       name, type, fields, visibility, item_order
    Missions/<slug>/items/<name>.json   title, natural language statement, source, tags
    Missions/<slug>/milestones.json     item, title, description

We edited the json prose after uploading it, and the platform keeps the version we submitted.

## Building

Slugs are hyphenated, so module names need French quotes:

    lake build 'Missions.«shao-three-units».Statements'

The p2m client's gate checks this tree in `statements` mode. Each draft item must end in `:= by sorry`. A hand-written `axiom`, a `native_decide`, or a compile error fails the check.

## The driver

`./upload.py <slug> <step>` runs each upload step through the p2m command-line client. It finds p2m on the path and reads the proposal id from the client's ledger.

    ./upload.py <slug> sweep      the duplicate sweep the gate demands
    ./upload.py <slug> dry        every item, exits nonzero if any refuses
    ./upload.py <slug> propose    create the draft
    ./upload.py <slug> items      add every item, in item_order
    ./upload.py <slug> finish     read-backs, then milestones
    ./upload.py <slug> order      set item_order and the goal

Get exit 0 from `dry` before every `propose`. The client's `submit`, `explain`, and `field-new` commands can't be undone, so they prompt a human at the terminal.

## Status

We read these platform figures on 2026-10-09. `p2m proposal <id>` refreshes them.

| Mission | Items | Platform status | Proved | Proposal id |
|---|---|---|---|---|
| `shao-three-units` | 10 theorems | Reviewed | 10 | `dc6c62ca-47f1-47e0-ad81-63ff92dc655f` |
| `z2n-five-eighths` | 1 definition, 10 theorems | Reviewed | 10 | `4c610437-1abb-40bf-9e2c-e0427f7b17a1` |
| `sidon-sqrt-n` | 17 theorems | Reviewed | 17 | `75753f60-2f7d-4a4a-b4e8-ea67c9106112` |
| `konyagin-unit-vectors` | 2 theorems | Reviewed | 2 | `591a6c72-bbae-444d-8ddb-e4b16a94e039` |

Other contributors proved every item of [`shao-three-units`](https://prove2.me/missions/Shao's_three_units_theorem%3A_density_5%2F8_forces_a_three-fold_additive_basis), [`z2n-five-eighths`](https://prove2.me/missions/Long-Wagner_Conjecture_5.1%3A_cube-free_subsets_of_Z%2F2%5EnZ_have_density_at_most_5%2F8), [`sidon-sqrt-n`](https://prove2.me/missions/The_Komlos-Sulyok-Szemeredi_bound%3A_every_finite_set_of_reals_has_a_Sidon_subset_of_size_c_sqrt_n), and [`konyagin-unit-vectors`](https://prove2.me/missions/Lovasz_Problem_11.8%3A_triangle-free_unit_vector_systems_sum_to_Theta(n%5E(2%2F3))). We submitted none of these proofs. Our own proofs in `shao-three-units/Development/` still build without a sorry.

`z2n-five-eighths/Research/` holds the SAT reproduction of `f(7) = 80`, three referee reports, and the solver script. Its UNSAT half lacks a certificate.

`extract-prose.py` copies the json prose into each `prose.md` so a linter can read it. Rerun it after editing json, then run `./extract-prose.py --check`.
