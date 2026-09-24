import Mathlib
open scoped Classical

/-!
Draft mission items for Shao's Corollary 1.5, each ending in `:= by sorry`.
Source: Xuancheng Shao, "A density version of the Vinogradov three primes
theorem", Duke Math. J. 163 (2014) 489-512, arXiv:1206.6139v2.
-/

namespace ShaoThreeUnits

/-- **The goal.** Shao's Corollary 1.5. -/
theorem three_units_of_five_eighths
    (m : ℕ) [NeZero m] (hodd : Odd m) (hsq : Squarefree m)
    (A : Finset (ZMod m)) (hA : ∀ a ∈ A, IsUnit a)
    (hcard : 5 * Nat.totient m < 8 * A.card) (x : ZMod m) :
    ∃ a ∈ A, ∃ b ∈ A, ∃ c ∈ A, a + b + c = x := by sorry

/-- **Milestone `card_U`.** The unit classes mod `m` number `φ(m)`. -/
theorem card_units_filter (m : ℕ) [NeZero m] :
    (Finset.univ.filter (fun x : ZMod m => IsUnit x)).card = Nat.totient m := by sorry

/-- **Milestone `cd_chowla`.** Cauchy-Davenport-Chowla for three sets mod a prime. -/
theorem cauchy_davenport_chowla (p : ℕ) (hp : p.Prime)
    (I J K : Finset (ZMod p)) (hI : I.Nonempty) (hJ : J.Nonempty)
    (hK : K.Nonempty) (hsum : p + 2 ≤ I.card + J.card + K.card) (x : ZMod p) :
    ∃ u ∈ I, ∃ v ∈ J, ∃ w ∈ K, u + v + w = x := by sorry

/-- **Milestone `lemma_2_1`.** Shao's Lemma 2.1, the symmetric averaging -/
theorem averaging_symmetric (n : ℕ) (hn : 6 ≤ n) (hev : Even n) (a : Fin n → ℝ)
    (hmono : Antitone a) (h0 : ∀ i, 0 ≤ a i) (h1 : ∀ i, a i ≤ 1)
    (htriple : ∀ i j k : Fin n, n ≤ (i : ℕ) + (j : ℕ) + (k : ℕ) →
      a i * a j + a j * a k + a k * a i ≤ 5 / 8 * (a i + a j + a k)) :
    (∑ i, a i) ≤ 5 / 8 * n := by sorry

/-- **Milestone `lemma_2_2`.** Shao's Lemma 2.2, the asymmetric averaging -/
theorem averaging_asymmetric (n : ℕ) (hn : 10 ≤ n) (hev : Even n)
    (a b c : Fin n → ℝ) (ha : Antitone a) (hb : Antitone b) (hc : Antitone c)
    (h0 : ∀ i, 0 ≤ a i ∧ 0 ≤ b i ∧ 0 ≤ c i)
    (h1 : ∀ i, a i ≤ 1 ∧ b i ≤ 1 ∧ c i ≤ 1)
    (htriple : ∀ i j k : Fin n, n ≤ (i : ℕ) + (j : ℕ) + (k : ℕ) →
      a i * b j + b j * c k + c k * a i ≤ 5 / 8 * (a i + b j + c k))
    (A B C : ℝ) (hA : A = (∑ i, a i) / n) (hB : B = (∑ i, b i) / n)
    (hC : C = (∑ i, c i) / n) :
    A * B + B * C + C * A ≤ 5 / 8 * (A + B + C) := by sorry

/-- **Milestone `lemma_2_3`.** Shao's Lemma 2.3, the finite check at `m = 15`. -/
theorem finite_check_fifteen (A B C : Finset (ZMod 15))
    (hA : ∀ a ∈ A, IsUnit a) (hB : ∀ b ∈ B, IsUnit b)
    (hC : ∀ c ∈ C, IsUnit c)
    (hsize : 5 * (A.card + B.card + C.card)
      < A.card * B.card + B.card * C.card + C.card * A.card) (x : ZMod 15) :
    ∃ a ∈ A, ∃ b ∈ B, ∃ c ∈ C, a + b + c = x := by sorry

/-- **Milestone `divisor_reduction`.** Shao's opening move in the proof of -/
theorem divisor_reduction (m M : ℕ) [NeZero m] [NeZero M] (hdvd : m ∣ M)
    (hM : ∀ g : ZMod M → ℝ, (∀ x, 0 ≤ g x) → (∀ x, g x ≤ 1) →
      (5 : ℝ) / 8 * (Nat.totient M)
          < (∑ x ∈ Finset.univ.filter (fun x : ZMod M => IsUnit x), g x) →
      ∀ y : ZMod M, ∃ b₁ : ZMod M, IsUnit b₁ ∧ ∃ b₂ : ZMod M, IsUnit b₂ ∧
        ∃ b₃ : ZMod M, IsUnit b₃ ∧ b₁ + b₂ + b₃ = y ∧
          0 < g b₁ * g b₂ * g b₃ ∧ 3 / 2 < g b₁ + g b₂ + g b₃) :
    ∀ f : ZMod m → ℝ, (∀ x, 0 ≤ f x) → (∀ x, f x ≤ 1) →
      (5 : ℝ) / 8 * (Nat.totient m)
          < (∑ x ∈ Finset.univ.filter (fun x : ZMod m => IsUnit x), f x) →
      ∀ y : ZMod m, ∃ a₁ : ZMod m, IsUnit a₁ ∧ ∃ a₂ : ZMod m, IsUnit a₂ ∧
        ∃ a₃ : ZMod m, IsUnit a₃ ∧ a₁ + a₂ + a₃ = y ∧
          0 < f a₁ * f a₂ * f a₃ ∧ 3 / 2 < f a₁ + f a₂ + f a₃ := by sorry

/-- **Milestone `prop_3_1`.** Shao's Proposition 3.1: the induction away from 3 -/
theorem induction_coprime_thirty (m : ℕ) [NeZero m] (hsq : Squarefree m)
    (hcop : Nat.Coprime m 30) (f : ZMod m → ℝ) (h0 : ∀ x, 0 ≤ f x)
    (h1 : ∀ x, f x ≤ 1)
    (hsum : (5 : ℝ) / 8 * (Nat.totient m)
      < (∑ x ∈ Finset.univ.filter (fun x : ZMod m => IsUnit x), f x))
    (x : ZMod m) :
    ∃ a : ZMod m, IsUnit a ∧ ∃ b : ZMod m, IsUnit b ∧ ∃ c : ZMod m, IsUnit c ∧
      a + b + c = x ∧
      5 / 8 * (f a + f b + f c) < f a * f b + f b * f c + f c * f a := by sorry

/-- **Milestone `prop_3_2`.** Shao's Proposition 3.2: the weighted case `m = 15`. -/
theorem weighted_fifteen (f₁ f₂ f₃ : ZMod 15 → ℝ)
    (h0 : ∀ x, 0 ≤ f₁ x ∧ 0 ≤ f₂ x ∧ 0 ≤ f₃ x)
    (h1 : ∀ x, f₁ x ≤ 1 ∧ f₂ x ≤ 1 ∧ f₃ x ≤ 1)
    (F₁ F₂ F₃ : ℝ)
    (hF₁ : F₁ = ∑ x ∈ Finset.univ.filter (fun x : ZMod 15 => IsUnit x), f₁ x)
    (hF₂ : F₂ = ∑ x ∈ Finset.univ.filter (fun x : ZMod 15 => IsUnit x), f₂ x)
    (hF₃ : F₃ = ∑ x ∈ Finset.univ.filter (fun x : ZMod 15 => IsUnit x), f₃ x)
    (hbig : 5 * (F₁ + F₂ + F₃) < F₁ * F₂ + F₂ * F₃ + F₃ * F₁) (x : ZMod 15) :
    ∃ a₁ : ZMod 15, IsUnit a₁ ∧ ∃ a₂ : ZMod 15, IsUnit a₂ ∧
      ∃ a₃ : ZMod 15, IsUnit a₃ ∧ a₁ + a₂ + a₃ = x ∧
        0 < f₁ a₁ * f₂ a₂ * f₃ a₃ ∧ 3 / 2 < f₁ a₁ + f₂ a₂ + f₃ a₃ := by sorry

/-- **Milestone `prop_1_4`.** Shao's Proposition 1.4, the weighted local result. -/
theorem weighted_local_result (m : ℕ) [NeZero m] (hodd : Odd m)
    (hsq : Squarefree m) (f : ZMod m → ℝ) (h0 : ∀ x, 0 ≤ f x)
    (h1 : ∀ x, f x ≤ 1)
    (hsum : (5 : ℝ) / 8 * (Nat.totient m)
      < (∑ x ∈ Finset.univ.filter (fun x : ZMod m => IsUnit x), f x))
    (x : ZMod m) :
    ∃ a₁ : ZMod m, IsUnit a₁ ∧ ∃ a₂ : ZMod m, IsUnit a₂ ∧
      ∃ a₃ : ZMod m, IsUnit a₃ ∧ a₁ + a₂ + a₃ = x ∧
        0 < f a₁ * f a₂ * f a₃ ∧ 3 / 2 < f a₁ + f a₂ + f a₃ := by sorry

end ShaoThreeUnits
