import Mathlib

/-!
Draft mission items for Erdos problem 530 (a Sidon subset of size `c√n`), each
ending in `:= by sorry`.
-/

namespace SidonSqrtN

/-! ## The goal -/

/-- The mission goal, Erdos problem 530. -/
theorem sidon_subset_sqrt :
    ∃ c : ℝ, 0 < c ∧ ∀ X : Finset ℝ, (∀ x ∈ X, 0 < x) →
      ∃ S ⊆ X, (∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, ∀ d ∈ S,
          a + b = c + d → (a = c ∧ b = d) ∨ (a = d ∧ b = c)) ∧
        c * Real.sqrt X.card ≤ (S.card : ℝ) := by sorry

/-! ## Milestone A: the cube-root bound for arbitrary reals -/

/-- Milestone `A1`: a Sidon subset of maximum cardinality exists. -/
theorem max_sidon_exists (X : Finset ℝ) :
    ∃ S ⊆ X, (∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, ∀ d ∈ S,
        a + b = c + d → (a = c ∧ b = d) ∨ (a = d ∧ b = c)) ∧
      ∀ T ⊆ X, (∀ a ∈ T, ∀ b ∈ T, ∀ c ∈ T, ∀ d ∈ T,
        a + b = c + d → (a = c ∧ b = d) ∨ (a = d ∧ b = c)) → T.card ≤ S.card := by sorry

/-- Milestone `A2`: maximality forces `|X| ≤ 3|S|^3`. -/
theorem max_sidon_cube (X S : Finset ℝ) (hSX : S ⊆ X)
    (hS : ∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, ∀ d ∈ S,
      a + b = c + d → (a = c ∧ b = d) ∨ (a = d ∧ b = c))
    (hmax : ∀ T ⊆ X, (∀ a ∈ T, ∀ b ∈ T, ∀ c ∈ T, ∀ d ∈ T,
      a + b = c + d → (a = c ∧ b = d) ∨ (a = d ∧ b = c)) → T.card ≤ S.card) :
    X.card ≤ 3 * S.card ^ 3 := by sorry

/-- Milestone `A3`: the cube-root bound. -/
theorem sidon_cbrt :
    ∃ c : ℝ, 0 < c ∧ ∀ X : Finset ℝ,
      ∃ S ⊆ X, (∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, ∀ d ∈ S,
          a + b = c + d → (a = c ∧ b = d) ∨ (a = d ∧ b = c)) ∧
        c * (X.card : ℝ) ^ ((1 : ℝ) / 3) ≤ (S.card : ℝ) := by sorry

/-! ## Milestone B: the Erdos-Turan lower bound for the interval

The set is `ET p = {2pk + (k² mod p) : k < p}`.
-/

/-- Milestone `B1`: the Erdos-Turan set has `p` elements. -/
theorem et_card (p : ℕ) (hp : 0 < p) :
    ((Finset.range p).image (fun k => 2 * p * k + k ^ 2 % p)).card = p := by sorry

/-- Milestone `B2`: the Erdos-Turan set is Sidon, for `p` prime. -/
theorem et_sidon (p : ℕ) (hp : p.Prime) :
    ∀ a ∈ (Finset.range p).image (fun k => 2 * p * k + k ^ 2 % p),
    ∀ b ∈ (Finset.range p).image (fun k => 2 * p * k + k ^ 2 % p),
    ∀ c ∈ (Finset.range p).image (fun k => 2 * p * k + k ^ 2 % p),
    ∀ d ∈ (Finset.range p).image (fun k => 2 * p * k + k ^ 2 % p),
      a + b = c + d → (a = c ∧ b = d) ∨ (a = d ∧ b = c) := by sorry

/-- Milestone `B3`: the Erdos-Turan set lives below `2p²`. -/
theorem et_range (p : ℕ) (hp : 0 < p) :
    ∀ x ∈ (Finset.range p).image (fun k => 2 * p * k + k ^ 2 % p),
      x < 2 * p ^ 2 := by sorry

/-- Milestone `B4`: a Sidon subset of `{0, ..., N-1}` of size at least `√N / 4`. -/
theorem sidon_in_range (N : ℕ) :
    ∃ S ⊆ Finset.range N, (∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, ∀ d ∈ S,
        a + b = c + d → (a = c ∧ b = d) ∨ (a = d ∧ b = c)) ∧
      Real.sqrt N / 4 ≤ (S.card : ℝ) := by sorry

/-! ## Milestone C: from the reals to the integers

A `ℚ`-linear functional keeps every additive relation in `X`, and a generic one
is injective on `X`.
-/

/-- Milestone `C1`: a `ℚ`-linear functional injective on `X`. -/
theorem q_separator (X : Finset ℝ) :
    ∃ f : ℝ →ₗ[ℚ] ℚ, Set.InjOn f (X : Set ℝ) := by sorry

/-- Milestone `C2`: an integer-valued Freiman 2-embedding of `X`. -/
theorem int_freiman (X : Finset ℝ) :
    ∃ φ : ℝ → ℤ, Set.InjOn φ (X : Set ℝ) ∧
      IsAddFreimanHom 2 (X : Set ℝ) Set.univ φ := by sorry

/-- Milestone `C3`: pull a Sidon set back from the integer image. -/
theorem sidon_transfer (X : Finset ℝ) (φ : ℝ → ℤ) (hinj : Set.InjOn φ (X : Set ℝ))
    (hfre : IsAddFreimanHom 2 (X : Set ℝ) Set.univ φ)
    (T : Finset ℤ) (hT : T ⊆ X.image φ)
    (hTS : ∀ a ∈ T, ∀ b ∈ T, ∀ c ∈ T, ∀ d ∈ T,
      a + b = c + d → (a = c ∧ b = d) ∨ (a = d ∧ b = c)) :
    ∃ S ⊆ X, (∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, ∀ d ∈ S,
        a + b = c + d → (a = c ∧ b = d) ∨ (a = d ∧ b = c)) ∧
      T.card ≤ S.card := by sorry

/-! ## Milestone D: the Komlos-Sulyok-Szemeredi compression chain, 1975

`A` reduces to `B` when every Sidon subset of `B` is matched by a Sidon subset
of `A` at least as large. A lower bound for `B` then transfers back to `A`. We
skip Lemma 1 (no proof in the paper), Lemmas 2 and 6 (our statements were
false), and Lemma 7 (not needed for Sidon sets).
-/

/-- Milestone `D0`, Remark 3: small remainders mod `q` are a Freiman 2-homomorphism. -/
theorem remark_3 (A : Finset ℤ) (q : ℤ) (k r : ℤ → ℤ) (hq : 0 < q)
    (hsmall : ∀ a ∈ A, a = k a * q + r a ∧ 4 * |r a| < q) :
    IsAddFreimanHom 2 (A : Set ℤ) Set.univ r := by sorry

/-- Milestone `D3`, the paper's Lemma 3: shrink the range from `|A|^3` to `|A|^(3/2)`. -/
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

/-- Milestone `D4`, the paper's Lemma 4: shrink the range from `|A|^(3/2)` to `|A|`. -/
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

/-- Milestone `D5`, the paper's Lemma 5: a positive `A` reduces to a set in `(0, |A|]`. -/
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

One averaging lemma over a real parameter replaces the whole D chain.
-/

/-- Milestone `E1`: Bailleul and Riblet's Lemma 2.3, compression into `ZMod m`. -/
theorem compression (A : Finset ℤ) (m : ℕ) (hm : 0 < m) :
    ∃ C ⊆ A, ∃ φ : ℤ → ZMod m,
      Set.InjOn φ (C : Set ℤ) ∧
      IsAddFreimanHom 2 (C : Set ℤ) Set.univ φ ∧
      (A.card : ℝ) / 2 - (A.card : ℝ) ^ 2 / (2 * m) ≤ (C.card : ℝ) := by sorry

/-- Milestone `E2`: averaging over the translates of a set in `ZMod m`. -/
theorem translate_averaging (m : ℕ) [NeZero m] (A B : Finset (ZMod m)) :
    ∃ i : ZMod m,
      (A.card * B.card : ℝ) / m ≤ (((B.image (· + i)) ∩ A).card : ℝ) := by sorry

end SidonSqrtN
