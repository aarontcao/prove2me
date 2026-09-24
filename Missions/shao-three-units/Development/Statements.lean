import Mathlib

/-!
Abbrevs for each proposition of Shao's argument, with companion `example`s at
concrete values. Source: Xuancheng Shao, "A density version of the Vinogradov
three primes theorem", Duke Math. J. 163 (2014) 489-512, arXiv:1206.6139v2.
-/
namespace ShaoThreeUnits.Statements

open scoped Classical
open Finset

/-- The units of `ZMod m`, as a `Finset (ZMod m)`. This is the ambient set the
whole problem lives in, since `A` is a subset of it and its size is `phi m`. -/
noncomputable def U (m : ℕ) [NeZero m] : Finset (ZMod m) :=
  Finset.univ.filter (fun x => IsUnit x)

/-! ## The goal -/

/-- Node `cor_1_5`, which is the question this development was built to answer. -/
abbrev Cor15 : Prop :=
  ∀ (m : ℕ) [NeZero m], Odd m → Squarefree m →
    ∀ A : Finset (ZMod m), A ⊆ U m → 5 * Nat.totient m < 8 * A.card →
      ∀ x : ZMod m, ∃ a ∈ A, ∃ b ∈ A, ∃ c ∈ A, a + b + c = x


/-! ## The weighted local result

`Cor15` is the `f = 1_A` case of `Prop14`. The induction that proves it cannot
be run on sets alone, so the whole proof works with functions into `[0,1]`.
-/

/-- Node `prop_1_4`. Shao's Proposition 1.4, the weighted local result. -/
abbrev Prop14 : Prop :=
  ∀ (m : ℕ) [NeZero m], Odd m → Squarefree m →
    ∀ f : ZMod m → ℝ, (∀ x, 0 ≤ f x) → (∀ x, f x ≤ 1) →
      (5 : ℝ) / 8 * (Nat.totient m) < (∑ x ∈ U m, f x) →
      ∀ x : ZMod m, ∃ a₁ ∈ U m, ∃ a₂ ∈ U m, ∃ a₃ ∈ U m, a₁ + a₂ + a₃ = x ∧
        0 < f a₁ * f a₂ * f a₃ ∧ 3 / 2 < f a₁ + f a₂ + f a₃


/-- Node `divisor_reduction`. Shao's opening move in the proof of Prop 1.4. -/
abbrev Prop14At (M : ℕ) [NeZero M] : Prop :=
  ∀ g : ZMod M → ℝ, (∀ x, 0 ≤ g x) → (∀ x, g x ≤ 1) →
    (5 : ℝ) / 8 * (Nat.totient M) < (∑ x ∈ U M, g x) →
    ∀ y : ZMod M, ∃ b₁ ∈ U M, ∃ b₂ ∈ U M, ∃ b₃ ∈ U M, b₁ + b₂ + b₃ = y ∧
      0 < g b₁ * g b₂ * g b₃ ∧ 3 / 2 < g b₁ + g b₂ + g b₃

abbrev DivisorReduction : Prop :=
  ∀ (m M : ℕ) [NeZero m] [NeZero M], m ∣ M → Prop14At M → Prop14At m


/-! ## The two halves of Proposition 1.4 -/

/-- Node `prop_3_1`. Shao's Proposition 3.1, the induction away from 3 and 5. -/
abbrev Prop31 : Prop :=
  ∀ (m : ℕ) [NeZero m], Squarefree m → Nat.Coprime m 30 →
    ∀ f : ZMod m → ℝ, (∀ x, 0 ≤ f x) → (∀ x, f x ≤ 1) →
      (5 : ℝ) / 8 * (Nat.totient m) < (∑ x ∈ U m, f x) →
      ∀ x : ZMod m, ∃ a ∈ U m, ∃ b ∈ U m, ∃ c ∈ U m, a + b + c = x ∧
        5 / 8 * (f a + f b + f c) < f a * f b + f b * f c + f c * f a


/-- Node `prop_3_2`. Shao's Proposition 3.2, the weighted case `m = 15`, which -/
abbrev Prop32 : Prop :=
  ∀ f₁ f₂ f₃ : ZMod 15 → ℝ,
    (∀ x, 0 ≤ f₁ x ∧ 0 ≤ f₂ x ∧ 0 ≤ f₃ x) →
    (∀ x, f₁ x ≤ 1 ∧ f₂ x ≤ 1 ∧ f₃ x ≤ 1) →
    ∀ F₁ F₂ F₃ : ℝ, F₁ = (∑ x ∈ U 15, f₁ x) → F₂ = (∑ x ∈ U 15, f₂ x) →
      F₃ = (∑ x ∈ U 15, f₃ x) →
      5 * (F₁ + F₂ + F₃) < F₁ * F₂ + F₂ * F₃ + F₃ * F₁ →
      ∀ x : ZMod 15, ∃ a₁ ∈ U 15, ∃ a₂ ∈ U 15, ∃ a₃ ∈ U 15, a₁ + a₂ + a₃ = x ∧
        0 < f₁ a₁ * f₂ a₂ * f₃ a₃ ∧ 3 / 2 < f₁ a₁ + f₂ a₂ + f₃ a₃


/-! ## The averaging lemmas -/

/-- Node `lemma_2_1`. Shao's Lemma 2.1, the symmetric averaging inequality. -/
abbrev Lemma21 : Prop :=
  ∀ (n : ℕ), 6 ≤ n → Even n → ∀ a : Fin n → ℝ, Antitone a →
    (∀ i, 0 ≤ a i) → (∀ i, a i ≤ 1) →
    (∀ i j k : Fin n, n ≤ (i : ℕ) + (j : ℕ) + (k : ℕ) →
      a i * a j + a j * a k + a k * a i ≤ 5 / 8 * (a i + a j + a k)) →
    (∑ i, a i) ≤ 5 / 8 * n


/-- Node `lemma_2_2`. Shao's Lemma 2.2, the asymmetric averaging inequality. -/
abbrev Lemma22 : Prop :=
  ∀ (n : ℕ), 10 ≤ n → Even n → ∀ a b c : Fin n → ℝ,
    Antitone a → Antitone b → Antitone c →
    (∀ i, 0 ≤ a i ∧ 0 ≤ b i ∧ 0 ≤ c i) →
    (∀ i, a i ≤ 1 ∧ b i ≤ 1 ∧ c i ≤ 1) →
    (∀ i j k : Fin n, n ≤ (i : ℕ) + (j : ℕ) + (k : ℕ) →
      a i * b j + b j * c k + c k * a i ≤ 5 / 8 * (a i + b j + c k)) →
    ∀ A B C : ℝ, A = (∑ i, a i) / n → B = (∑ i, b i) / n → C = (∑ i, c i) / n →
      A * B + B * C + C * A ≤ 5 / 8 * (A + B + C)


/-! ## The finite and support nodes -/

/-- Node `lemma_2_3`. Shao's Lemma 2.3, the finite check at `m = 15`. -/
abbrev Lemma23 : Prop :=
  ∀ A B C : Finset (ZMod 15), A ⊆ U 15 → B ⊆ U 15 → C ⊆ U 15 →
    5 * (A.card + B.card + C.card)
        < A.card * B.card + B.card * C.card + C.card * A.card →
    ∀ x : ZMod 15, ∃ a ∈ A, ∃ b ∈ B, ∃ c ∈ C, a + b + c = x


/-- Node `cd_chowla`. Cauchy-Davenport-Chowla for three sets mod a prime. -/
abbrev CDChowla : Prop :=
  ∀ (p : ℕ), p.Prime → ∀ I J K : Finset (ZMod p),
    I.Nonempty → J.Nonempty → K.Nonempty →
    p + 2 ≤ I.card + J.card + K.card →
    ∀ x : ZMod p, ∃ u ∈ I, ∃ v ∈ J, ∃ w ∈ K, u + v + w = x


/-- Node `card_U`. The unit classes mod `m` number `phi m`. -/
abbrev CardU : Prop :=
  ∀ (m : ℕ) [NeZero m], (U m).card = Nat.totient m


/-! ## Anti-vacuity

A clean audit says that a theorem follows from standard axioms, and it does not
say whether the hypotheses can be met, so the witnesses below are the
human check that the nodes above are not vacuous. Each of them must be proved,
and none of them may ever be `sorry`ed.
-/

/-- The hypotheses of `Cor15` can be met, since `m = 15` is odd and squarefree and -/
example : Odd 15 ∧ Squarefree 15 ∧ 5 * Nat.totient 15 < 8 * 8 := by
  refine ⟨⟨7, by norm_num⟩, by decide +kernel, by decide⟩

/-- Sharpness, as a plain arithmetic fact. At `m = 15` a set of size 5 gives -/
example : 5 * Nat.totient 15 = 8 * 5 := by decide

/-- The `m = 15` nodes are not quantified over an empty class either, because -/
example : Nat.totient 15 = 8 := by decide

end ShaoThreeUnits.Statements
