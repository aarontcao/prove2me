# Coreflections transport along a root datum isogeny

## Problem

Let $P_1$ and $P_2$ be root pairings over $\mathbb{Q}$, with character spaces $M_1, M_2$ and cocharacter spaces $N_1, N_2$. An isogeny of root data supplies a transposed pair of isomorphisms

$$\psi^{\ast} : M_2 \xrightarrow{\sim} M_1, \qquad
\psi_{\ast} : N_1 \xrightarrow{\sim} N_2,
\qquad \langle \psi^{\ast} m, n \rangle_1 = \langle m, \psi_{\ast} n \rangle_2 .$$

Fix indices $i_1$, $i_2$ and a scalar $c \in \mathbb{Q}$ matching one root line and one coroot line:

$$\psi^{\ast}(\alpha_2) = c \alpha_1, \qquad
\psi_{\ast}(\alpha_1^\vee) = c \alpha_2^\vee .$$

Then $\psi_{\ast}$ intertwines the two coreflections:

$$\psi_{\ast}\bigl(s_{\alpha_1}^\vee(x)\bigr)
= s_{\alpha_2}^\vee\bigl(\psi_{\ast}(x)\bigr) \qquad \text{for every } x \in N_1 .$$

Here $s_{\alpha_i}^\vee(x) = x - \langle \alpha_i, x\rangle \alpha_i^\vee$ is the coreflection, which Mathlib calls `RootPairing.coreflection`.

## The idea

Expand both sides. The same scalar $c$ appears on each by different routes.

$$\underbrace{\psi_{\ast} x - \langle \alpha_1, x\rangle \cdot c \alpha_2^\vee}_{\text{left: } c \text{ comes from } \psi_{\ast}(\alpha_1^\vee) = c \alpha_2^\vee}
\qquad
\underbrace{\psi_{\ast} x - c \langle \alpha_1, x\rangle \cdot \alpha_2^\vee}_{\text{right: } c \text{ comes from transposition}} $$

On the right, the transpose axiom at $m = \alpha_2$ turns $\langle \alpha_2, \psi_{\ast} x\rangle$ into $\langle \psi^{\ast}\alpha_2, x\rangle = c \langle \alpha_1, x\rangle$. The two expressions differ only in the order of a product in $\mathbb{Q}$.

## Where it comes from

Why may the same $c$ appear on both sides? Ngô's definition matches *lines*, not vectors: $\psi^{\ast}$ carries the line $\mathbb{Q}\alpha_2$ onto $\mathbb{Q}\alpha_1$, and $\psi_{\ast}$ does the same for coroot lines. So a priori the roots and coroots get scalars $c$ and $c'$.

Transposition and the normalization $\langle \alpha, \alpha^\vee\rangle = 2$ force $c = c'$. Read the transpose axiom at the pair $(\alpha_2, \alpha_1^\vee)$:

$$\langle \psi^{\ast}\alpha_2, \alpha_1^\vee\rangle_1
= \langle \alpha_2, \psi_{\ast}\alpha_1^\vee\rangle_2 .$$

Substituting both hypotheses gives $c \cdot 2 = c' \cdot 2$, so $c = c'$. In Lean, against Mathlib:

```lean
example {ι₁ ι₂ M₁ N₁ M₂ N₂ : Type*} [AddCommGroup M₁] [Module ℚ M₁]
    [AddCommGroup N₁] [Module ℚ N₁] [AddCommGroup M₂] [Module ℚ M₂]
    [AddCommGroup N₂] [Module ℚ N₂]
    (P₁ : RootPairing ι₁ ℚ M₁ N₁) (P₂ : RootPairing ι₂ ℚ M₂ N₂)
    (psiStar : M₂ ≃ₗ[ℚ] M₁) (psiLower : N₁ ≃ₗ[ℚ] N₂)
    (htrans : ∀ (m : M₂) (n : N₁),
      P₁.toLinearMap (psiStar m) n = P₂.toLinearMap m (psiLower n))
    (i₁ : ι₁) (i₂ : ι₂) (c c' : ℚ)
    (hroot : psiStar (P₂.root i₂) = c • P₁.root i₁)
    (hcoroot : psiLower (P₁.coroot i₁) = c' • P₂.coroot i₂) :
    c = c' := by
  have h := htrans (P₂.root i₂) (P₁.coroot i₁)
  rw [hroot, hcoroot] at h
  simp only [map_smul, LinearMap.smul_apply, P₁.root_coroot_two,
    P₂.root_coroot_two, smul_eq_mul] at h
  linarith
```

The proof below reads the same identity at $(\alpha_2, x)$.

## The proof

Claim 1 is that $\langle \alpha_2, \psi_{\ast} x\rangle = c \langle \alpha_1, x\rangle$ for every $x \in N_1$. It is the transpose axiom at $m = \alpha_2$ and $n = x$, with $\psi^{\ast}(\alpha_2) = c \alpha_1$ substituted.

Claim 2 is the theorem. By linearity of $\psi_{\ast}$ the left side is

$$\psi_{\ast}\bigl(x - \langle \alpha_1, x\rangle \alpha_1^\vee\bigr)
= \psi_{\ast} x - \langle \alpha_1, x\rangle \psi_{\ast}(\alpha_1^\vee)
= \psi_{\ast} x - \langle \alpha_1, x\rangle c \alpha_2^\vee .$$

By Claim 1 the right side is

$$s_{\alpha_2}^\vee(\psi_{\ast} x)
= \psi_{\ast} x - \langle \alpha_2, \psi_{\ast} x\rangle \alpha_2^\vee
= \psi_{\ast} x - c \langle \alpha_1, x\rangle \alpha_2^\vee .$$

The scalars $\langle \alpha_1, x\rangle \cdot c$ and $c \cdot \langle \alpha_1, x\rangle$ are equal in $\mathbb{Q}$. $\square$

## What the hypotheses do

Of the seven fields of the isogeny structure, the proof uses only `h.transpose`. It never touches `root_line`, `root_line_surjective`, `coroot_line`, `coroot_line_surjective`, `simple_mem`, `simple_surjective`, or the simple root sets `b₁` and `b₂`. So the theorem holds for any transposed pair of linear isomorphisms with a matched root and coroot. The upstream simple-root field also puts the negative of each simple root into the simple set. Ngô's definition doesn't, but the proof never reads that field.

The statement doesn't need $c \ne 0$. The normalization $\langle \alpha, \alpha^\vee \rangle = 2$ makes $\alpha_2 \ne 0$. Since $\psi^{\ast}$ is injective, $\psi^{\ast}(\alpha_2) = c \alpha_1$ is nonzero, so $c \ne 0$.

The field $\mathbb{Q}$ doesn't matter either. Ngô works over $\mathbb{Q}$ because an isogeny becomes an isomorphism only after tensoring with $\mathbb{Q}$, but the proof works over any commutative ring. This snippet is the same proof with the isogeny cut down to its transpose field:

```lean
example {R ι₁ ι₂ M₁ N₁ M₂ N₂ : Type*} [CommRing R] [AddCommGroup M₁]
    [Module R M₁] [AddCommGroup N₁] [Module R N₁] [AddCommGroup M₂]
    [Module R M₂] [AddCommGroup N₂] [Module R N₂]
    (P₁ : RootPairing ι₁ R M₁ N₁) (P₂ : RootPairing ι₂ R M₂ N₂)
    (psiStar : M₂ ≃ₗ[R] M₁) (psiLower : N₁ ≃ₗ[R] N₂)
    (htrans : ∀ (m : M₂) (n : N₁),
      P₁.toLinearMap (psiStar m) n = P₂.toLinearMap m (psiLower n))
    (i₁ : ι₁) (i₂ : ι₂) (c : R)
    (hroot : psiStar (P₂.root i₂) = c • P₁.root i₁)
    (hcoroot : psiLower (P₁.coroot i₁) = c • P₂.coroot i₂) (x : N₁) :
    psiLower (P₁.coreflection i₁ x) = P₂.coreflection i₂ (psiLower x) := by
  have key : P₂.toLinearMap (P₂.root i₂) (psiLower x)
      = c * P₁.toLinearMap (P₁.root i₁) x := by
    rw [← htrans (P₂.root i₂) x, hroot]
    simp
  simp only [RootPairing.coreflection, Module.reflection_apply, map_sub,
    map_smul, hcoroot, key, smul_smul, mul_comm]
```

## Context

The definition is from Ngô's proof of the fundamental lemma for Lie algebras.

> Bao Châu Ngô, *Le lemme fondamental pour les algèbres de Lie*, Publications
> Mathématiques de l'IHÉS **111** (2010), 1-169.
> [numdam.org](https://www.numdam.org/item/PMIHES_2010__111__1_0/),
> doi:10.1007/s10240-010-0026-7.

Définition 1.12.1 asks for mutually transposed isomorphisms of $\mathbb{Q}$-vector spaces

$$\psi^{\ast} : X^{\ast}(T_2) \otimes \mathbb{Q} \to X^{\ast}(T_1) \otimes \mathbb{Q},
\qquad \psi_{\ast} : X_{\ast}(T_1) \otimes \mathbb{Q} \to X_{\ast}(T_2) \otimes \mathbb{Q}.$$

The map $\psi^{\ast}$ must carry the set of lines $\mathbb{Q}\alpha_2$ bijectively onto the set of lines $\mathbb{Q}\alpha_1$, matching simple root lines with simple root lines. The same goes for $\psi_{\ast}$ on the coroot lines. This is the input to Théorème 1.12.7, the non-standard fundamental lemma conjectured by Waldspurger.

Ngô never names the scalar. We name it so the lemma can talk about one index pair at a time, and the agreement $c = c'$ is the price.

## Formalization

`RootPairing.coreflection i` is defined as `Module.reflection (P.root_coroot_two i)`, so `Module.reflection_apply` unfolds it to `x - (P.root' i) x • P.coroot i`, where `root'` abbreviates `P.toLinearMap (P.root i)`. The solution is the second snippet above with `h.transpose` in place of `htrans` and $\mathbb{Q}$ in place of `R`: one `have` and one `simp only`. The `mul_comm` in that list matches $\langle \alpha_1, x\rangle \cdot c$ with $c \cdot \langle \alpha_1, x\rangle$. The other lemmas unfold the coreflection and substitute the two hypotheses.

The solution file restates the theorem to avoid importing the upstream `sorry`.

## What it does not say

The solution lacks a companion `example` at concrete data. Contradictory hypotheses would make it vacuous, but the identity map rules that out. On any root pairing with at least one root, take $i_1 = i_2$, $c = 1$, and empty simple root sets, and every hypothesis holds.

The theorem is one compatibility inside the combinatorial input to the non-standard fundamental lemma. It doesn't touch orbital integrals or the fundamental lemma itself.
