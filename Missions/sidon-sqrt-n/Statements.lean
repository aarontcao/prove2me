import Mathlib

/-!
Draft mission items for Erdos problem 530, a Sidon subset of size `c√n`, each
ending in `:= by sorry`. Ported from `Workbench/Bench/sidon-sqrt-n/`.
-/

namespace SidonSqrtN

/-! ## The goal -/

/-- **The goal.** Erdos problem 530. -/
theorem sidon_subset_sqrt :
    ∃ c : ℝ, 0 < c ∧ ∀ X : Finset ℝ, (∀ x ∈ X, 0 < x) →
      ∃ S ⊆ X, (∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, ∀ d ∈ S,
          a + b = c + d → (a = c ∧ b = d) ∨ (a = d ∧ b = c)) ∧
        c * Real.sqrt X.card ≤ (S.card : ℝ) := by sorry

/-! ## Milestone A: the cube-root bound for arbitrary reals -/

/-- **Milestone `A1`.** A Sidon subset of maximum cardinality exists. -/
theorem max_sidon_exists (X : Finset ℝ) :
    ∃ S ⊆ X, (∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, ∀ d ∈ S,
        a + b = c + d → (a = c ∧ b = d) ∨ (a = d ∧ b = c)) ∧
      ∀ T ⊆ X, (∀ a ∈ T, ∀ b ∈ T, ∀ c ∈ T, ∀ d ∈ T,
        a + b = c + d → (a = c ∧ b = d) ∨ (a = d ∧ b = c)) → T.card ≤ S.card := by sorry

/-- **Milestone `A2`.** Maximality forces `|X| ≤ 3|S|^3`. -/
theorem max_sidon_cube (X S : Finset ℝ) (hSX : S ⊆ X)
    (hS : ∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, ∀ d ∈ S,
      a + b = c + d → (a = c ∧ b = d) ∨ (a = d ∧ b = c))
    (hmax : ∀ T ⊆ X, (∀ a ∈ T, ∀ b ∈ T, ∀ c ∈ T, ∀ d ∈ T,
      a + b = c + d → (a = c ∧ b = d) ∨ (a = d ∧ b = c)) → T.card ≤ S.card) :
    X.card ≤ 3 * S.card ^ 3 := by sorry

/-- **Milestone `A3`.** The cube-root bound. -/
theorem sidon_cbrt :
    ∃ c : ℝ, 0 < c ∧ ∀ X : Finset ℝ,
      ∃ S ⊆ X, (∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, ∀ d ∈ S,
          a + b = c + d → (a = c ∧ b = d) ∨ (a = d ∧ b = c)) ∧
        c * (X.card : ℝ) ^ ((1 : ℝ) / 3) ≤ (S.card : ℝ) := by sorry

/-! ## Milestone B: the Erdos-Turan lower bound for the interval

The set is `ET p = {2pk + (k² mod p) : k < p}`. This is the one place in the
whole development where a Sidon set is built rather than found.
-/

/-- **Milestone `B1`.** The Erdos-Turan set has exactly `p` elements. -/
theorem et_card (p : ℕ) (hp : 0 < p) :
    ((Finset.range p).image (fun k => 2 * p * k + k ^ 2 % p)).card = p := by sorry

/-- **Milestone `B2`.** The Erdos-Turan set is Sidon, for `p` prime. -/
theorem et_sidon (p : ℕ) (hp : p.Prime) :
    ∀ a ∈ (Finset.range p).image (fun k => 2 * p * k + k ^ 2 % p),
    ∀ b ∈ (Finset.range p).image (fun k => 2 * p * k + k ^ 2 % p),
    ∀ c ∈ (Finset.range p).image (fun k => 2 * p * k + k ^ 2 % p),
    ∀ d ∈ (Finset.range p).image (fun k => 2 * p * k + k ^ 2 % p),
      a + b = c + d → (a = c ∧ b = d) ∨ (a = d ∧ b = c) := by sorry

/-- **Milestone `B3`.** The Erdos-Turan set lives below `2p²`. -/
theorem et_range (p : ℕ) (hp : 0 < p) :
    ∀ x ∈ (Finset.range p).image (fun k => 2 * p * k + k ^ 2 % p),
      x < 2 * p ^ 2 := by sorry

/-- **Milestone `B4`.** A Sidon subset of `{0, ..., N-1}` of size at least -/
theorem sidon_in_range (N : ℕ) :
    ∃ S ⊆ Finset.range N, (∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, ∀ d ∈ S,
        a + b = c + d → (a = c ∧ b = d) ∨ (a = d ∧ b = c)) ∧
      Real.sqrt N / 4 ≤ (S.card : ℝ) := by sorry

/-! ## Milestone C: from the reals to the integers

Only the forward direction is needed. A finite set of reals spans a finite
dimensional `ℚ`-vector space, and a generic rational functional separates its
points while preserving every additive relation.
-/

/-- **Milestone `C1`.** A `ℚ`-linear functional injective on `X`. -/
theorem q_separator (X : Finset ℝ) :
    ∃ f : ℝ →ₗ[ℚ] ℚ, Set.InjOn f (X : Set ℝ) := by sorry

/-- **Milestone `C2`.** An integer-valued Freiman 2-embedding of `X`. -/
theorem int_freiman (X : Finset ℝ) :
    ∃ φ : ℝ → ℤ, Set.InjOn φ (X : Set ℝ) ∧
      IsAddFreimanHom 2 (X : Set ℝ) Set.univ φ := by sorry

/-- **Milestone `C3`.** Pull a Sidon set back from the integer image. -/
theorem sidon_transfer (X : Finset ℝ) (φ : ℝ → ℤ) (hinj : Set.InjOn φ (X : Set ℝ))
    (hfre : IsAddFreimanHom 2 (X : Set ℝ) Set.univ φ)
    (T : Finset ℤ) (hT : T ⊆ X.image φ)
    (hTS : ∀ a ∈ T, ∀ b ∈ T, ∀ c ∈ T, ∀ d ∈ T,
      a + b = c + d → (a = c ∧ b = d) ∨ (a = d ∧ b = c)) :
    ∃ S ⊆ X, (∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, ∀ d ∈ S,
        a + b = c + d → (a = c ∧ b = d) ∨ (a = d ∧ b = c)) ∧
      T.card ≤ S.card := by sorry

/-! ## Milestone D: the Komlos-Sulyok-Szemeredi compression chain, 1975

The reduction relation is written out at each use. `A` reduces to `B` when every
Sidon subset of `B` is matched by a Sidon subset of `A` at least as large. Note
the direction: a reduct is a set that is no easier, so a lower bound proved for
`B` transfers back to `A`.

Lemma 1 of the paper is stated there without proof. Lemmas 2 and 6 are absent
here because the bench's own renderings of them are refuted, and Lemma 7 is the
non-translation-invariant case, which Sidon does not need.
-/

/-- **Milestone `D0`.** The paper's Remark 3, the workhorse of every later lemma. -/
theorem remark_3 (A : Finset ℤ) (q : ℤ) (k r : ℤ → ℤ) (hq : 0 < q)
    (hsmall : ∀ a ∈ A, a = k a * q + r a ∧ 4 * |r a| < q) :
    IsAddFreimanHom 2 (A : Set ℤ) Set.univ r := by sorry

/-- **Milestone `D3`.** The paper's Lemma 3, the second range reduction. -/
theorem lemma_3 :
    ∃ c : ℝ, 0 < c ∧ ∀ (A : Finset ℤ) (M : ℕ), (∀ a ∈ A, 0 < a ∧ a ≤ (M : ℤ)) →
      M ≤ A.card ^ 3 →
      ∃ B : Finset ℤ,
        (∀ T ⊆ B, (∀ a ∈ T, ∀ b ∈ T, ∀ c ∈ T, ∀ d ∈ T,
            a + b = c + d → (a = c ∧ b = d) ∨ (a = d ∧ b = c)) →
          ∃ S ⊆ A, (∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, ∀ d ∈ S,
              a + b = c + d → (a = c ∧ b = d) ∨ (a = d ∧ b = c)) ∧
            T.card ≤ S.card) ∧
        (∀ b ∈ B, 0 < b ∧ b ^ 2 ≤ (A.card : ℤ) ^ 3) ∧
        c * A.card ≤ (B.card : ℝ) := by sorry

/-- **Milestone `D4`.** The paper's Lemma 4, the third range reduction. -/
theorem lemma_4 :
    ∃ c : ℝ, 0 < c ∧ ∀ (A : Finset ℤ) (M : ℕ), (∀ a ∈ A, 0 < a ∧ a ≤ (M : ℤ)) →
      (M : ℤ) ^ 2 ≤ (A.card : ℤ) ^ 3 →
      ∃ B : Finset ℤ,
        (∀ T ⊆ B, (∀ a ∈ T, ∀ b ∈ T, ∀ c ∈ T, ∀ d ∈ T,
            a + b = c + d → (a = c ∧ b = d) ∨ (a = d ∧ b = c)) →
          ∃ S ⊆ A, (∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, ∀ d ∈ S,
              a + b = c + d → (a = c ∧ b = d) ∨ (a = d ∧ b = c)) ∧
            T.card ≤ S.card) ∧
        (∀ b ∈ B, 0 < b ∧ b ≤ (A.card : ℤ)) ∧
        c * A.card ≤ (B.card : ℝ) := by sorry

/-- **Milestone `D5`.** The paper's Lemma 5, the interface of the whole chain. -/
theorem lemma_5 :
    ∃ c : ℝ, 0 < c ∧ ∀ A : Finset ℤ, (∀ a ∈ A, 0 < a) →
      ∃ B : Finset ℤ,
        (∀ T ⊆ B, (∀ a ∈ T, ∀ b ∈ T, ∀ c ∈ T, ∀ d ∈ T,
            a + b = c + d → (a = c ∧ b = d) ∨ (a = d ∧ b = c)) →
          ∃ S ⊆ A, (∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, ∀ d ∈ S,
              a + b = c + d → (a = c ∧ b = d) ∨ (a = d ∧ b = c)) ∧
            T.card ≤ S.card) ∧
        (∀ b ∈ B, 0 < b ∧ b ≤ (A.card : ℤ)) ∧
        c * A.card ≤ (B.card : ℝ) := by sorry

/-! ## Milestone E: the Bailleul-Riblet route, 2026

One averaging lemma over a real parameter replaces the whole D chain, and no
prime counting is needed anywhere.
-/

/-- Milestone `E1`, the compression lemma, which is Lemma 2.3 of Bailleul and -/
theorem compression (A : Finset ℤ) (m : ℕ) (hm : 0 < m) :
    ∃ C ⊆ A, ∃ φ : ℤ → ZMod m,
      Set.InjOn φ (C : Set ℤ) ∧
      IsAddFreimanHom 2 (C : Set ℤ) Set.univ φ ∧
      (A.card : ℝ) / 2 - (A.card : ℝ) ^ 2 / (2 * m) ≤ (C.card : ℝ) := by sorry

/-- **Milestone `E2`.** Averaging over the translates of a set in `ZMod m`. -/
theorem translate_averaging (m : ℕ) [NeZero m] (A B : Finset (ZMod m)) :
    ∃ i : ZMod m,
      (A.card * B.card : ℝ) / m ≤ (((B.image (· + i)) ∩ A).card : ℝ) := by sorry

end SidonSqrtN
