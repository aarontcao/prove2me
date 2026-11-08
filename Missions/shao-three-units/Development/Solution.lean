/-
Copyright 2026 Aaron Cao.
SPDX-License-Identifier: AGPL-3.0-or-later
-/
import Missions.«shao-three-units».Development.Proof

/-!
The mission goal from `cor_1_5`, turning `∀ a ∈ A, IsUnit a` into `A ⊆ U m`.
-/

open scoped Classical

theorem ShaoThreeUnits.three_units_of_five_eighths
    (m : ℕ) [NeZero m] (hodd : Odd m) (hsq : Squarefree m)
    (A : Finset (ZMod m)) (hA : ∀ a ∈ A, IsUnit a)
    (hcard : 5 * Nat.totient m < 8 * A.card) (x : ZMod m) :
    ∃ a ∈ A, ∃ b ∈ A, ∃ c ∈ A, a + b + c = x :=
  ShaoThreeUnits.Proof.cor_1_5 m hodd hsq A
    (fun a ha => by simpa [ShaoThreeUnits.Statements.U] using hA a ha) hcard x
