# Proof development

Our proofs of the `shao-three-units` mission items. None of them uses `sorry`.

## Mission items

| Shao | declaration here | mission item | platform |
|---|---|---|---|
| Corollary 1.5 | `ShaoThreeUnits.three_units_of_five_eighths` | `three_units_of_five_eighths` | Proved |
| Proposition 1.4 | `Proof.prop_1_4` | `weighted_local_result` | Proved |
| Proposition 3.1 | `Proof.prop_3_1` | `induction_coprime_thirty` | Proved |
| Proposition 3.2 | `Proof.prop_3_2` | `weighted_fifteen` | Proved |
| Lemma 2.3 | `Proof.lemma_2_3` | `finite_check_fifteen` | Proved |
| (divisor reduction) | `Proof.divisor_reduction` | `divisor_reduction` | Proved |
| Lemma 2.1 | `Proof.lemma_2_1` | `averaging_symmetric` | Proved |
| Lemma 2.2 | `Proof.lemma_2_2` | `averaging_asymmetric` | Proved |
| (Cauchy-Davenport-Chowla) | `Proof.cd_chowla` | `cauchy_davenport_chowla` | Proved |
| (unit count) | `Proof.card_U` | `card_units_filter` | Proved |

We read the platform column on 2026-10-09.

## Departures from the paper

Lemma 2.3 uses a Chinese Remainder reduction instead of a computer search. Proposition 3.2 gives explicit Farkas certificates instead of a solver call. `formalization.yaml` records both.

## Build

    lake build 'Missions.«shao-three-units».Development.Solution'
