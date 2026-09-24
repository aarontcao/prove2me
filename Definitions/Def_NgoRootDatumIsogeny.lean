import Mathlib

/-!
# Isogenies of root data and paired reductive groups

Formalization layer for §1.12 of B.-C. Ngô, *Le lemme fondamental pour les algèbres de
Lie*, Publ. Math. IHÉS **111** (2010), 1–169, the combinatorial input to the *non-standard
fundamental lemma* of Waldspurger (Theorem 1.12.7 of loc. cit.).

For two pinned split reductive groups `G₁`, `G₂` with maximal tori `T₁`, `T₂`, an isogeny
of root data (Définition 1.12.1) is a pair of mutually transposed isomorphisms of
`ℚ`-vector spaces
`ψ^* : X^*(T₂) ⊗ ℚ → X^*(T₁) ⊗ ℚ` and `ψ_* : X_*(T₁) ⊗ ℚ → X_*(T₂) ⊗ ℚ`
such that `ψ^*` carries the set of lines `ℚα₂` (`α₂ ∈ Φ₂`) bijectively onto the set of
lines `ℚα₁` (`α₁ ∈ Φ₁`), matching the lines of simple roots with the lines of simple
roots, and such that `ψ_*` has the corresponding property for the coroot lines.

Root data are modelled by `RootPairing ι ℚ M N` with `M` the character space and `N` the
cocharacter space; a choice of simple roots is recorded as a subset of the index type.
-/

namespace NgoFL

/-- An isogeny of root data in the sense of Ngô, Définition 1.12.1.  Here `b₁`, `b₂` index
the chosen simple roots of the two systems. -/
structure IsRootDatumIsogeny {ι₁ ι₂ M₁ N₁ M₂ N₂ : Type*} [AddCommGroup M₁] [Module ℚ M₁]
    [AddCommGroup N₁] [Module ℚ N₁] [AddCommGroup M₂] [Module ℚ M₂] [AddCommGroup N₂]
    [Module ℚ N₂] (P₁ : RootPairing ι₁ ℚ M₁ N₁) (P₂ : RootPairing ι₂ ℚ M₂ N₂)
    (b₁ : Set ι₁) (b₂ : Set ι₂) (psiStar : M₂ ≃ₗ[ℚ] M₁) (psiLower : N₁ ≃ₗ[ℚ] N₂) :
    Prop where
  /-- `ψ^*` and `ψ_*` are transposes of one another. -/
  transpose : ∀ (m : M₂) (n : N₁), P₁.toLinearMap (psiStar m) n = P₂.toLinearMap m (psiLower n)
  /-- Every root line of `Φ₂` is carried to a root line of `Φ₁`. -/
  root_line : ∀ i₂ : ι₂, ∃ i₁ : ι₁, ∃ c : ℚ, c ≠ 0 ∧ psiStar (P₂.root i₂) = c • P₁.root i₁
  /-- Every root line of `Φ₁` arises this way. -/
  root_line_surjective :
    ∀ i₁ : ι₁, ∃ i₂ : ι₂, ∃ c : ℚ, c ≠ 0 ∧ psiStar (P₂.root i₂) = c • P₁.root i₁
  /-- Every coroot line of `Φ₁^∨` is carried to a coroot line of `Φ₂^∨`. -/
  coroot_line : ∀ i₁ : ι₁, ∃ i₂ : ι₂, ∃ c : ℚ, c ≠ 0 ∧ psiLower (P₁.coroot i₁) = c • P₂.coroot i₂
  /-- Every coroot line of `Φ₂^∨` arises this way. -/
  coroot_line_surjective :
    ∀ i₂ : ι₂, ∃ i₁ : ι₁, ∃ c : ℚ, c ≠ 0 ∧ psiLower (P₁.coroot i₁) = c • P₂.coroot i₂
  /-- Lines of simple roots go to lines of simple roots. -/
  simple_mem : ∀ i₂ ∈ b₂, ∀ (i₁ : ι₁) (c : ℚ), c ≠ 0 →
    psiStar (P₂.root i₂) = c • P₁.root i₁ → i₁ ∈ b₁
  /-- Every line of a simple root of `Φ₁` comes from a line of a simple root of `Φ₂`. -/
  simple_surjective : ∀ i₁ ∈ b₁, ∃ i₂ ∈ b₂, ∃ c : ℚ, c ≠ 0 ∧
    psiStar (P₂.root i₂) = c • P₁.root i₁

/-- The index `|Λ₁ / (Λ₁ ∩ Λ₂)|` of two subgroups of a common ambient group. -/
noncomputable def latticeIndex {V : Type*} [AddCommGroup V] (L₁ L₂ : AddSubgroup V) : ℕ :=
  Nat.card (L₁ ⧸ (L₁ ⊓ L₂).addSubgroupOf L₁)

/-- `O` is a *good* base ring for the pair of lattices `Λ₁`, `Λ₂` when both indices -/
def IsGoodBase {V : Type*} [AddCommGroup V] (O : Type*) [CommRing O]
    (L₁ L₂ : AddSubgroup V) : Prop :=
  IsUnit ((latticeIndex L₁ L₂ : ℕ) : O) ∧ IsUnit ((latticeIndex L₂ L₁ : ℕ) : O)

end NgoFL
