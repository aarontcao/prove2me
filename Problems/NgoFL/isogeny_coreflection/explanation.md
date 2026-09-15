# Coreflections transport along a root datum isogeny

## Problem

Let $P_1$ and $P_2$ be root pairings over $\mathbb{Q}$, with character spaces
$M_1, M_2$ and cocharacter spaces $N_1, N_2$. An isogeny of root data supplies a
transposed pair of isomorphisms

$$\psi^{\ast} : M_2 \xrightarrow{\sim} M_1, \qquad
\psi_{\ast} : N_1 \xrightarrow{\sim} N_2,
\qquad \langle \psi^{\ast} m, n \rangle_1 = \langle m, \psi_{\ast} n \rangle_2 .$$

Fix indices $i_1$, $i_2$ and a scalar $c \in \mathbb{Q}$ matching one root line
and one coroot line:

$$\psi^{\ast}(\alpha_2) = c \alpha_1, \qquad
\psi_{\ast}(\alpha_1^\vee) = c \alpha_2^\vee .$$

Then $\psi_{\ast}$ intertwines the two coreflections:

$$\psi_{\ast}\bigl(s_{\alpha_1}^\vee(x)\bigr)
= s_{\alpha_2}^\vee\bigl(\psi_{\ast}(x)\bigr) \qquad \text{for every } x \in N_1 .$$

Here $s_{\alpha}^\vee$ is the coreflection, $s_{\alpha_i}^\vee(x) = x -
\langle \alpha_i, x\rangle \alpha_i^\vee$, which is `RootPairing.coreflection`
in Mathlib.

## The idea

Expand both sides. The same scalar $c$ has to appear on each, and it arrives by
two different routes.

$$\underbrace{\psi_{\ast} x - \langle \alpha_1, x\rangle \cdot c \alpha_2^\vee}_{\text{left: } c \text{ comes from } \psi_{\ast}(\alpha_1^\vee) = c \alpha_2^\vee}
\qquad
\underbrace{\psi_{\ast} x - c \langle \alpha_1, x\rangle \cdot \alpha_2^\vee}_{\text{right: } c \text{ comes from transposition}} $$

The left side picks up $c$ from the coroot hypothesis, after linearity pulls
the pairing out front. The right side picks it up from the transpose axiom read
at $m = \alpha_2$, which turns $\langle \alpha_2, \psi_{\ast} x\rangle$ into
$\langle \psi^{\ast}\alpha_2, x\rangle = c \langle \alpha_1, x\rangle$. The two
expressions differ by the order of a product in $\mathbb{Q}$, so they are
equal.

## Where it comes from

Why is the same $c$ allowed on both sides at all?

Ngô's definition matches *lines*, not vectors. It says that $\psi^{\ast}$ carries
the line $\mathbb{Q}\alpha_2$ onto the line $\mathbb{Q}\alpha_1$, and that
$\psi_{\ast}$ does the same for the coroot lines. Extracting a scalar from each
statement gives two of them, say $c$ for the roots and $c'$ for the coroots,
with no reason yet to be equal. The theorem as stated uses one letter for both,
which looks like a hypothesis quietly strengthened.

It is not. Transposition forces $c = c'$, and the normalization
$\langle \alpha, \alpha^\vee\rangle = 2$ is what does it. Read the transpose
axiom at the pair $(\alpha_2, \alpha_1^\vee)$:

$$\langle \psi^{\ast}\alpha_2, \alpha_1^\vee\rangle_1
= \langle \alpha_2, \psi_{\ast}\alpha_1^\vee\rangle_2 .$$

Substituting both hypotheses turns this into $c \cdot 2 = c' \cdot 2$, so
$c = c'$. Machine-checked, and reproducible by pasting this into a file with
Mathlib on the path:

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

That is the whole idea of the theorem, one step earlier. Transposition is a
single identity between two pairings, and reading it at different arguments
yields both the agreement of the scalars and the transport of the
coreflections. The proof below is that identity read at $(\alpha_2, x)$ instead
of at $(\alpha_2, \alpha_1^\vee)$.

## The proof

**Claim 1.** $\langle \alpha_2, \psi_{\ast} x\rangle = c \langle \alpha_1, x\rangle$
for every $x \in N_1$.

Read the transpose axiom at $m = \alpha_2$ and $n = x$, then substitute
$\psi^{\ast}(\alpha_2) = c \alpha_1$ and pull the scalar out of the linear form.

**Claim 2.** The two sides of the theorem agree.

Unfold the left side and apply linearity of $\psi_{\ast}$:

$$\psi_{\ast}\bigl(x - \langle \alpha_1, x\rangle \alpha_1^\vee\bigr)
= \psi_{\ast} x - \langle \alpha_1, x\rangle \psi_{\ast}(\alpha_1^\vee)
= \psi_{\ast} x - \langle \alpha_1, x\rangle c \alpha_2^\vee .$$

Unfold the right side and apply Claim 1:

$$s_{\alpha_2}^\vee(\psi_{\ast} x)
= \psi_{\ast} x - \langle \alpha_2, \psi_{\ast} x\rangle \alpha_2^\vee
= \psi_{\ast} x - c \langle \alpha_1, x\rangle \alpha_2^\vee .$$

The two scalars are $\langle \alpha_1, x\rangle \cdot c$ and $c \cdot \langle
\alpha_1, x\rangle$, equal in $\mathbb{Q}$. $\square$

## Why the hypotheses bite

**Six of the seven fields of the isogeny structure go unused.** The proof uses
only `h.transpose`. `root_line`, `root_line_surjective`,
`coroot_line`, `coroot_line_surjective`, `simple_mem`, and `simple_surjective`
never appear, and neither do the sets of simple roots `b₁` and `b₂`.

So the theorem proved here is more general than the theorem stated. It holds
for any transposed pair of linear isomorphisms with a matched root and coroot,
with no isogeny anywhere in sight. The isogeny hypothesis is what supplies such
a pair in practice, and it is why the statement is phrased this way, but the
argument never touches it.

**The statement carries no hypothesis $c \ne 0$, and needs none.** The reason
is the same normalization as above. A root pairing satisfies
$\langle \alpha, \alpha^\vee \rangle = 2$, so $\alpha_2 \ne 0$; the map
$\psi^{\ast}$ is injective, so $\psi^{\ast}(\alpha_2) \ne 0$; and
$\psi^{\ast}(\alpha_2) = c \alpha_1$ then forces $c \ne 0$. The hypothesis is
derivable, so omitting it costs nothing and the $c = 0$ instance is unreachable.

**Rationality is doing nothing.** The proof needs a commutative base ring and
the pairing normalization. It uses no other property of $\mathbb{Q}$. Ngô works with
$\mathbb{Q}$-vector spaces because the isogeny is only an isomorphism after
tensoring with $\mathbb{Q}$, so the coefficient field comes from the source and
this lemma never asks for it.

All three claims above are one snippet, which is the same proof with the
isogeny structure replaced by its transpose field and $\mathbb{Q}$ replaced by
an arbitrary commutative ring. It compiles unchanged against the pinned
Mathlib.

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

The definition being formalized is Ngô's, from the paper that proves the
fundamental lemma for Lie algebras. Titles are quoted exactly as published.

> Bao Châu Ngô, *Le lemme fondamental pour les algèbres de Lie*, Publications
> Mathématiques de l'IHÉS **111** (2010), 1-169.
> [numdam.org](https://www.numdam.org/item/PMIHES_2010__111__1_0/),
> doi:10.1007/s10240-010-0026-7.

Section 1.12 of that paper is titled *Le lemme fondamental non standard*, and
Définition 1.12.1 is the definition this file formalizes. Read from the Numdam
scan, it asks for a pair of mutually transposed isomorphisms of
$\mathbb{Q}$-vector spaces,

$$\psi^{\ast} : X^{\ast}(T_2) \otimes \mathbb{Q} \to X^{\ast}(T_1) \otimes \mathbb{Q},
\qquad \psi_{\ast} : X_{\ast}(T_1) \otimes \mathbb{Q} \to X_{\ast}(T_2) \otimes \mathbb{Q}.$$

It then asks that $\psi^{\ast}$ carry the set of lines $\mathbb{Q}\alpha_2$
bijectively onto the set of lines $\mathbb{Q}\alpha_1$, matching simple root
lines with simple root lines. The same is demanded of $\psi_{\ast}$ on the coroot
lines. Théorème 1.12.7, in the same section, is the
non-standard fundamental lemma conjectured by Waldspurger.

What the source does not cover: Ngô states the definition and never names the
scalar, because a statement about lines does not need one. Naming it is a
formalization choice, made so that a lemma can be stated pointwise about one
index pair at a time. The agreement of the two scalars, derived above, is the
price of that choice, and it is the reason the theorem reads as though it
assumes something extra.

## Formalization

Mathlib does most of this. `RootPairing.coreflection i` is defined as
`Module.reflection (P.root_coroot_two i)`, so `Module.reflection_apply` unfolds
it to `x - (P.root' i) x • P.coroot i`, where `root'` is the abbreviation for
`P.toLinearMap (P.root i)`. The whole proof is one `have` and one `simp only`.

```lean
theorem solution ... :
    psiLower (P₁.coreflection i₁ x) = P₂.coreflection i₂ (psiLower x) := by
  have key : P₂.toLinearMap (P₂.root i₂) (psiLower x)
      = c * P₁.toLinearMap (P₁.root i₁) x := by
    rw [← h.transpose (P₂.root i₂) x, hroot]
    simp
  simp only [RootPairing.coreflection, Module.reflection_apply, map_sub,
    map_smul, hcoroot, key, smul_smul, mul_comm]
```

The one detail to point out is that `mul_comm` sits in the `simp only` list.
That is the last step of the argument, the one where
$\langle \alpha_1, x\rangle \cdot c$ meets $c \cdot \langle \alpha_1,
x\rangle$, and it is easy to read past it as boilerplate. Everything before it
is unfolding.

The statement is restated in the solution file instead of imported from the
upstream statement file. That file proves its theorem with `sorry`, and
importing it would pull `sorryAx` into the axiom closure, so the audit would
pass while proving nothing. The shared definition file is imported, since it
carries a structure and no proofs.

## What it does not say

**There is no companion example, and that is a real gap.** The convention on
this box is that every theorem of substance gets a companion `example`
instantiating it at concrete data, because a statement with contradictory
hypotheses typechecks perfectly and proves nothing. This solution file has
none. The derivation of $c \ne 0$ above rules out the one obvious way for the
hypotheses to be unsatisfiable. That is not the same as exhibiting a root
datum, an index pair, and a scalar that satisfy all of them at once. The gap is
named here instead of quietly closed, because closing it means editing a
solution that has already been submitted.

This explanation was also written after the fact. The solution was submitted
before an explanation was part of the routine, and `meta.json` records that.

The theorem is one compatibility inside the combinatorial input to the
non-standard fundamental lemma. It says nothing about orbital integrals,
nothing about the fundamental lemma itself, and nothing about the other
conditions in Définition 1.12.1, which the proof never reads.

The axiom closure stays within `propext`, `Classical.choice`, and `Quot.sound`.
