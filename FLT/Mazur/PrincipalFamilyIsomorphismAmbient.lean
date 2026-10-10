/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PrincipalFamilyIsomorphismOpens

/-!
# Ambient chart systems for genuine finite overlap models

The same index recovers the full source charts, and the overlap open immersions
commute with all transitions. Thus the open maps belong to an inverse system,
rather than being unrelated stagewise choices.
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry

namespace FLT.Mazur.FiniteTypeRelationModel

universe u v

variable {R : Type u} [CommRing R] {ι : Type v} [Finite ι]
  {A : ι → Type u} [∀ i, CommRing (A i)] [∀ i, Algebra R (A i)]
  [∀ i, Algebra.FiniteType R (A i)]
  {B : Type u} [CommRing B] [Algebra R B] [Algebra.FiniteType R B]
  (a : ∀ i, A i) (b : B) (e : ∀ i, Localization.Away (a i) ≃ₐ[R] Localization.Away b)

/-- Forget an isomorphic overlap family down to one ambient chart's relation set. -/
def principalIsoFamilyChartIndex (i : ι) :
    PrincipalFamilyIsomorphismStage a b e ⥤ Finset (relationIdeal R (A i)) :=
  principalFamilyIsomorphismIndex a b e ⋙
    principalFamilySourceIndex a b (fun i ↦ (e i).toAlgHom) i

/-- Isomorphism models remain cofinal in every ambient chart. -/
instance principalIsoFamilyChartIndexFinal (i : ι) :
    (principalIsoFamilyChartIndex a b e i).Final := by
  dsimp [principalIsoFamilyChartIndex]
  infer_instance

/-- Ambient chart rings on the overlap isomorphism index. -/
def principalIsoFamilyChartDiagram (i : ι) :
    PrincipalFamilyIsomorphismStage a b e ⥤ CommRingCat.{u} :=
  principalIsoFamilyChartIndex a b e i ⋙ FiniteRelationModel.ringDiagram R (relationIdeal R (A i))

/-- The original full chart receives the compatible finite-stage projections. -/
def principalIsoFamilyChartCocone (i : ι) : Cocone (principalIsoFamilyChartDiagram a b e i) :=
  (algebraCocone R (A i)).whisker (principalIsoFamilyChartIndex a b e i)

/-- Imposing overlap invertibility preserves the original ambient chart ring. -/
def principalIsoFamilyChartIsColimit (i : ι) : IsColimit (principalIsoFamilyChartCocone a b e i) :=
  (Functor.Final.isColimitWhiskerEquiv (principalIsoFamilyChartIndex a b e i)
    (algebraCocone R (A i))).symm (algebraIsColimit R (A i))

/-- The original ambient spectrum maps to its chart models. -/
def principalIsoFamilyChartCone (i : ι) :
    Cone ((principalIsoFamilyChartDiagram a b e i).op ⋙ Scheme.Spec) :=
  Scheme.Spec.mapCone (principalIsoFamilyChartCocone a b e i).op

/-- The full source chart is recovered on the isomorphism subsystem. -/
def principalIsoFamilyChartIsLimit (i : ι) : IsLimit (principalIsoFamilyChartCone a b e i) :=
  isLimitOfPreserves Scheme.Spec (principalIsoFamilyChartIsColimit a b e i).op

/-- Principal-open inclusions commute with the ambient chart transitions. -/
def principalIsoFamilyInclusion (i : ι) :
    (principalIsoFamilySourceDiagram a b e i).op ⋙ Scheme.Spec ⟶
      (principalIsoFamilyChartDiagram a b e i).op ⋙ Scheme.Spec where
  app x := PrincipalLocalizationSquare.inclusion
    (Ideal.Quotient.mk _ (principalRepresentative R (A i) (a i)))
  naturality x y h := by
    exact (PrincipalLocalizationSquare.condition
      (FiniteRelationModel.transition R (relationIdeal R (A i))
        ((leOfHom h.unop).choose i)).toRingHom
      (Ideal.Quotient.mk _ (principalRepresentative R (A i) (a i)))).symm

/-- All actual overlap open immersions form a natural transformation to the full chart system. -/
def principalIsoFamilyOpenMap (i : ι) :
    (principalIsoFamilyTargetDiagram a b e).op ⋙ Scheme.Spec ⟶
      (principalIsoFamilyChartDiagram a b e i).op ⋙ Scheme.Spec :=
  (principalIsoFamilySchemeIso a b e i).hom ≫ principalIsoFamilyInclusion a b e i

/-- Every component of the natural overlap map is an open immersion. -/
instance principalIsoFamilyOpenMap_isOpenImmersion (i : ι)
    (x : (PrincipalFamilyIsomorphismStage a b e)ᵒᵖ) :
    IsOpenImmersion ((principalIsoFamilyOpenMap a b e i).app x) :=
  principalIsoFamilyOpen_isOpenImmersion a b e x.unop i

end FLT.Mazur.FiniteTypeRelationModel
