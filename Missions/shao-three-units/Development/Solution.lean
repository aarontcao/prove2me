/-
Copyright 2026 Aaron Cao.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
import Missions.«shao-three-units».Development.Proof

/-!
Proved solution. Bridges the unit hypothesis from the development's
`A ⊆ U m` to the mission's `∀ a ∈ A, IsUnit a`.
-/

open scoped Classical

theorem ShaoThreeUnits.three_units_of_five_eighths
    (m : ℕ) [NeZero m] (hodd : Odd m) (hsq : Squarefree m)
    (A : Finset (ZMod m)) (hA : ∀ a ∈ A, IsUnit a)
    (hcard : 5 * Nat.totient m < 8 * A.card) (x : ZMod m) :
    ∃ a ∈ A, ∃ b ∈ A, ∃ c ∈ A, a + b + c = x :=
  ShaoThreeUnits.Proof.cor_1_5 m hodd hsq A
    (fun a ha => by simpa [ShaoThreeUnits.Statements.U] using hA a ha) hcard x
