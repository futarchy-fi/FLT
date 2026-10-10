/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PrincipalOccurrencePatchNaturality

/-!
# Identifying patch domains with equal images

Equal patch images in a shared overlap give actual scheme isomorphisms,
even for different incoming ambient charts. Their inverse, composition and
refinement laws follow by cancellation of the original open embeddings.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.FiniteTypeRelationModel

universe u v w z

variable {R : Type u} [CommRing R] {ι : Type v} {κ : Type w} {J : ι → Type z}
  {A : ι → Type u} [∀ i, CommRing (A i)] [∀ i, Algebra R (A i)]
  [∀ i, Algebra.FiniteType R (A i)]
  {B : κ → Type u} [∀ j, CommRing (B j)] [∀ j, Algebra R (B j)]
  [∀ j, Algebra.FiniteType R (B j)]
  {dst : ∀ i, J i → κ} {a : ∀ i, J i → A i} {b : ∀ j, B j}
  {f : ∀ i k, Localization.Away (a i k) →ₐ[R] Localization.Away (b (dst i k))}
  (x : PrincipalOccurrenceStage dst a b f) (hx : ∀ i k, Function.Bijective (x.hom i k))
  {j : κ} (p q : PrincipalOccurrencePatch (dst := dst) j)
  (h : (principalOccurrencePatchOpen x hx p).opensRange =
    (principalOccurrencePatchOpen x hx q).opensRange)

/-- Equal images identify the actual patch schemes over the shared overlap. -/
def principalOccurrencePatchImageIso :
    principalOccurrencePatchScheme x p ≅ principalOccurrencePatchScheme x q :=
  IsOpenImmersion.isoOfRangeEq (principalOccurrencePatchOpen x hx p)
    (principalOccurrencePatchOpen x hx q) (congrArg SetLike.coe h)

/-- The image isomorphism retains the shared-overlap embedding. -/
@[reassoc] theorem principalOccurrencePatchImageIso_fac :
    (principalOccurrencePatchImageIso x hx p q h).hom ≫ principalOccurrencePatchOpen x hx q =
      principalOccurrencePatchOpen x hx p :=
  IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _

/-- Exchanging the two patches gives the inverse isomorphism. -/
theorem principalOccurrencePatchImageIso_symm :
    (principalOccurrencePatchImageIso x hx p q h).symm =
      principalOccurrencePatchImageIso x hx q p h.symm := by
  apply Iso.ext
  apply (cancel_mono (principalOccurrencePatchOpen x hx p)).mp
  exact (IsOpenImmersion.isoOfRangeEq_inv_fac _ _ (congrArg SetLike.coe h)).trans
    (principalOccurrencePatchImageIso_fac x hx q p h.symm).symm

/-- Image identifications satisfy the full three-patch composition law. -/
@[reassoc] theorem principalOccurrencePatchImageIso_comp
    (r : PrincipalOccurrencePatch (dst := dst) j)
    (hqr : (principalOccurrencePatchOpen x hx q).opensRange =
      (principalOccurrencePatchOpen x hx r).opensRange) :
    (principalOccurrencePatchImageIso x hx p q h).hom ≫
        (principalOccurrencePatchImageIso x hx q r hqr).hom =
      (principalOccurrencePatchImageIso x hx p r (h.trans hqr)).hom := by
  apply (cancel_mono (principalOccurrencePatchOpen x hx r)).mp
  rw [Category.assoc, principalOccurrencePatchImageIso_fac,
    principalOccurrencePatchImageIso_fac, principalOccurrencePatchImageIso_fac]

/-- Identifications commute with every refinement preserving the two image equalities. -/
@[reassoc] theorem principalOccurrencePatchImageIso_natural
    {y : PrincipalOccurrenceStage dst a b f} (hxy : x ≤ y)
    (hy : ∀ i k, Function.Bijective (y.hom i k))
    (h' : (principalOccurrencePatchOpen y hy p).opensRange =
      (principalOccurrencePatchOpen y hy q).opensRange) :
    principalOccurrencePatchTransition hxy hx hy p ≫
        (principalOccurrencePatchImageIso x hx p q h).hom =
      (principalOccurrencePatchImageIso y hy p q h').hom ≫
        principalOccurrencePatchTransition hxy hx hy q := by
  apply (cancel_mono (principalOccurrencePatchOpen x hx q)).mp
  rw [Category.assoc, Category.assoc, principalOccurrencePatchImageIso_fac,
    principalOccurrencePatchTransition_fac, principalOccurrencePatchTransition_fac,
    principalOccurrencePatchImageIso_fac_assoc]

end FLT.Mazur.FiniteTypeRelationModel
