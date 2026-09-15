import Mathlib
import Definitions.Def_NgoRootDatumIsogeny

namespace NgoFL

theorem isogeny_coreflection {ι₁ ι₂ M₁ N₁ M₂ N₂ : Type*} [AddCommGroup M₁] [Module ℚ M₁]
    [AddCommGroup N₁] [Module ℚ N₁] [AddCommGroup M₂] [Module ℚ M₂] [AddCommGroup N₂]
    [Module ℚ N₂] (P₁ : RootPairing ι₁ ℚ M₁ N₁) (P₂ : RootPairing ι₂ ℚ M₂ N₂)
    (b₁ : Set ι₁) (b₂ : Set ι₂) (psiStar : M₂ ≃ₗ[ℚ] M₁) (psiLower : N₁ ≃ₗ[ℚ] N₂)
    (h : IsRootDatumIsogeny P₁ P₂ b₁ b₂ psiStar psiLower)
    (i₁ : ι₁) (i₂ : ι₂) (c : ℚ)
    (hroot : psiStar (P₂.root i₂) = c • P₁.root i₁)
    (hcoroot : psiLower (P₁.coroot i₁) = c • P₂.coroot i₂) (x : N₁) :
    psiLower (P₁.coreflection i₁ x) = P₂.coreflection i₂ (psiLower x) := by sorry

end NgoFL