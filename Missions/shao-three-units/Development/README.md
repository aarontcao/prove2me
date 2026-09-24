# Proof development

Our proofs of the `shao-three-units` mission items, 153 declarations that never use `sorry`.

## Which proof discharges which mission item

| Shao | declaration here | mission item | platform |
|---|---|---|---|
| Corollary 1.5 | `Solution.three_units_of_five_eighths` | `three_units_of_five_eighths` | Proved |
| Proposition 1.4 | `Proof.prop_1_4` | `weighted_local_result` | Proved |
| Proposition 3.1 | `Proof.prop_3_1` | `induction_coprime_thirty` | Proved |
| Proposition 3.2 | `Proof.prop_3_2` | `weighted_fifteen` | Proved |
| Lemma 2.3 | `Proof.lemma_2_3` | `finite_check_fifteen` | Proved |
| (divisor reduction) | `Proof.divisor_reduction` | `divisor_reduction` | Proved |
| Lemma 2.1 | `Proof.lemma_2_1` | `averaging_symmetric` | Proved |
| Lemma 2.2 | `Proof.lemma_2_2` | `averaging_asymmetric` | Proved |
| (Cauchy-Davenport-Chowla) | `Proof.cd_chowla` | `cauchy_davenport_chowla` | Proved |
| (unit count) | `Proof.card_U` | `card_units_filter` | Proved |

The platform column is the platform's report as read on 2026-09-23, never a verdict here. Other contributors proved the six items this directory had been holding for submission.

## Departures from the paper

Lemma 2.3 uses Chinese Remainder reduction instead of a computer search, and Proposition 3.2 gives explicit Farkas certificates instead of a solver call. Both are recorded in `formalization.yaml`.

## Provenance

Ported on 2026-09-19 from a standalone repository that was never published. Build by name:

    lake build 'Missions.«shao-three-units».Development.Solution'
