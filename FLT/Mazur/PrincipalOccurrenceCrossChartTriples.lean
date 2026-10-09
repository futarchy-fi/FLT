/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PrincipalOccurrenceCrossChartIntersections

/-!
# Global triple comparisons across occurrence charts

Three double-open patches may come from different ambient charts and
have different outer overlap labels. Their common domain is a scheme
fiber product over the shared overlap. Cyclic changes of presentation
satisfy the cocycle on that entire domain.
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry

namespace FLT.Mazur.FiniteTypeRelationModel

universe u v w z

variable {R : Type u} [CommRing R] {ι : Type v} {κ : Type w} {J : ι → Type z}
  {A : ι → Type u} [∀ i, CommRing (A i)] [∀ i, Algebra R (A i)]
  [∀ i, Algebra.FiniteType R (A i)]
  {B : κ → Type u} [∀ j, CommRing (B j)] [∀ j, Algebra R (B j)]
  [∀ j, Algebra.FiniteType R (B j)]
  {dst : ∀ i, J i → κ} {a : ∀ i, J i → A i} {b : ∀ j, B j}
  {f : ∀ i e, Localization.Away (a i e) →ₐ[R] Localization.Away (b (dst i e))}
  (x : PrincipalOccurrenceStage dst a b f) (hx : ∀ i e, Function.Bijective (x.hom i e))


variable {j : κ} (p q r : PrincipalOccurrencePatch (dst := dst) j)

/-- The simultaneous intersection of three patches in a literal shared overlap. -/
abbrev principalOccurrenceCrossTriple : Scheme.{u} :=
  pullback (principalOccurrenceCrossOpen x hx p q) (principalOccurrencePatchOpen x hx r)

/-- Its first patch coordinate, in the first ambient chart. -/
abbrev principalOccurrenceCrossTripleFirst :
    principalOccurrenceCrossTriple x hx p q r ⟶ principalOccurrencePatchScheme x p :=
  pullback.fst _ _ ≫ principalOccurrenceCrossLeft x hx p q

/-- Its second patch coordinate, in the second ambient chart. -/
abbrev principalOccurrenceCrossTripleSecond :
    principalOccurrenceCrossTriple x hx p q r ⟶ principalOccurrencePatchScheme x q :=
  pullback.fst _ _ ≫ principalOccurrenceCrossRight x hx p q

/-- Its third patch coordinate, in the third ambient chart. -/
abbrev principalOccurrenceCrossTripleThird :
    principalOccurrenceCrossTriple x hx p q r ⟶ principalOccurrencePatchScheme x r :=
  pullback.snd _ _

/-- The actual triple embedding in the shared overlap scheme. -/
def principalOccurrenceCrossTripleOpen : principalOccurrenceCrossTriple x hx p q r ⟶
    Spec (.of (PrincipalStage R (B j) (b j) (x.target j))) :=
  pullback.fst _ _ ≫ principalOccurrenceCrossOpen x hx p q

/-- This triple comparison domain is open in the shared overlap. -/
instance principalOccurrenceCrossTripleOpen_isOpenImmersion :
    IsOpenImmersion (principalOccurrenceCrossTripleOpen x hx p q r) := by
  dsimp only [principalOccurrenceCrossTripleOpen]
  infer_instance

/-- The triple has exactly the intersection of all three patch images. -/
theorem principalOccurrenceCrossTriple_opensRange :
    (principalOccurrenceCrossTripleOpen x hx p q r).opensRange =
      ((principalOccurrencePatchOpen x hx p).opensRange ⊓
        (principalOccurrencePatchOpen x hx q).opensRange) ⊓
          (principalOccurrencePatchOpen x hx r).opensRange := by
  dsimp only [principalOccurrenceCrossTripleOpen]
  rw [Scheme.Hom.opensRange_comp, Scheme.Hom.opensRange_pullbackFst,
    Scheme.Hom.image_preimage_eq_opensRange_inf, principalOccurrenceCross_opensRange]

/-- Cyclic presentations of the cross-chart triple are canonically isomorphic. -/
def principalOccurrenceCrossTripleRotate :
    principalOccurrenceCrossTriple x hx p q r ≅ principalOccurrenceCrossTriple x hx q r p :=
  IsOpenImmersion.isoOfRangeEq (principalOccurrenceCrossTripleOpen x hx p q r)
    (principalOccurrenceCrossTripleOpen x hx q r p) (by
      have h : (principalOccurrenceCrossTripleOpen x hx p q r).opensRange =
          (principalOccurrenceCrossTripleOpen x hx q r p).opensRange := by
        rw [principalOccurrenceCrossTriple_opensRange, principalOccurrenceCrossTriple_opensRange]
        ac_rfl
      exact congrArg SetLike.coe h)

/-- Rotating the presentation leaves the shared-overlap embedding unchanged. -/
@[reassoc (attr := simp)] theorem principalOccurrenceCrossTripleRotate_fac :
    (principalOccurrenceCrossTripleRotate x hx p q r).hom ≫
      principalOccurrenceCrossTripleOpen x hx q r p =
        principalOccurrenceCrossTripleOpen x hx p q r :=
  IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _

/-- The inverse rotation also retains the global shared-overlap embedding. -/
@[reassoc (attr := simp)] theorem principalOccurrenceCrossTripleRotate_inv_fac :
    (principalOccurrenceCrossTripleRotate x hx p q r).inv ≫
      principalOccurrenceCrossTripleOpen x hx p q r =
        principalOccurrenceCrossTripleOpen x hx q r p :=
  IsOpenImmersion.isoOfRangeEq_inv_fac _ _ _

/-- The two successive changes equal the direct inverse change on the full triple scheme. -/
theorem principalOccurrenceCrossTripleRotate_cocycle :
    (principalOccurrenceCrossTripleRotate x hx p q r).hom ≫
      (principalOccurrenceCrossTripleRotate x hx q r p).hom =
        (principalOccurrenceCrossTripleRotate x hx r p q).inv := by
  rw [← cancel_mono (principalOccurrenceCrossTripleOpen x hx r p q)]
  simp only [Category.assoc, principalOccurrenceCrossTripleRotate_fac,
    principalOccurrenceCrossTripleRotate_inv_fac]

/-- Three cyclic changes compose to the identity morphism. -/
theorem principalOccurrenceCrossTripleRotate_cycle :
    (principalOccurrenceCrossTripleRotate x hx p q r).hom ≫
      (principalOccurrenceCrossTripleRotate x hx q r p).hom ≫
        (principalOccurrenceCrossTripleRotate x hx r p q).hom = 𝟙 _ := by
  rw [← Category.assoc, principalOccurrenceCrossTripleRotate_cocycle, Iso.inv_hom_id]

end FLT.Mazur.FiniteTypeRelationModel
