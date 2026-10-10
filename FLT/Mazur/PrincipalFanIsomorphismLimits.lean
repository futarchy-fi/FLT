/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PrincipalFanIsomorphismStages
public import FLT.Mazur.FiniteTypePrincipalApproximation

/-!
# Recovering one ambient chart and all its overlap isomorphisms

The common ambient chart and its distinct principal opens are inverse limits
on the same isomorphism index. The coordinate maps are natural isomorphisms,
and their colimit is exactly the given original coordinate identification.
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry

namespace FLT.Mazur.FiniteTypeRelationModel

universe u v

variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
  [Algebra.FiniteType R A] {ι : Type v} [Finite ι]
  {B : ι → Type u} [∀ i, CommRing (B i)] [∀ i, Algebra R (B i)]
  [∀ i, Algebra.FiniteType R (B i)]
  (a : ι → A) (b : ∀ i, B i)
  (e : ∀ i, Localization.Away (a i) ≃ₐ[R] Localization.Away (b i))

/-- The single ambient chart diagram shared by all outgoing overlaps. -/
def principalIsoFanChartDiagram : PrincipalFanIsomorphismStage a b e ⥤ CommRingCat.{u} :=
  principalIsoFanSourceIndex a b e ⋙ FiniteRelationModel.ringDiagram R (relationIdeal R A)

/-- Each principal open is localized on that same ambient relation index. -/
def principalIsoFanSourceDiagram (i : ι) :
    PrincipalFanIsomorphismStage a b e ⥤ CommRingCat.{u} :=
  principalIsoFanSourceIndex a b e ⋙ FiniteRelationLocalization.ringDiagram R
    (relationIdeal R A) (principalRepresentative R A (a i))

/-- Independent target principal charts on the common fan index. -/
def principalIsoFanTargetDiagram (i : ι) :
    PrincipalFanIsomorphismStage a b e ⥤ CommRingCat.{u} :=
  principalIsoFanTargetIndex a b e i ⋙ FiniteRelationLocalization.ringDiagram R
    (relationIdeal R (B i)) (principalRepresentative R (B i) (b i))

/-- The original ambient chart receives the finite-stage projections. -/
def principalIsoFanChartCocone : Cocone (principalIsoFanChartDiagram a b e) :=
  (algebraCocone R A).whisker (principalIsoFanSourceIndex a b e)

/-- Projections to each original principal open of the shared chart. -/
def principalIsoFanSourceCocone (i : ι) : Cocone (principalIsoFanSourceDiagram a b e i) :=
  (principalAlgebraCocone R A (a i)).whisker (principalIsoFanSourceIndex a b e)

/-- Projections to each original target principal ring. -/
def principalIsoFanTargetCocone (i : ι) : Cocone (principalIsoFanTargetDiagram a b e i) :=
  (principalAlgebraCocone R (B i) (b i)).whisker (principalIsoFanTargetIndex a b e i)

/-- The full original chart is recovered while all its overlap maps are invertible. -/
def principalIsoFanChartIsColimit : IsColimit (principalIsoFanChartCocone a b e) :=
  (Functor.Final.isColimitWhiskerEquiv (principalIsoFanSourceIndex a b e)
    (algebraCocone R A)).symm (algebraIsColimit R A)

/-- Every original source principal ring is recovered on the shared chart index. -/
def principalIsoFanSourceIsColimit (i : ι) : IsColimit (principalIsoFanSourceCocone a b e i) :=
  (Functor.Final.isColimitWhiskerEquiv (principalIsoFanSourceIndex a b e)
    (principalAlgebraCocone R A (a i))).symm (principalAlgebraIsColimit R A (a i))

/-- Every original target ring is recovered on the same index. -/
def principalIsoFanTargetIsColimit (i : ι) : IsColimit (principalIsoFanTargetCocone a b e i) :=
  (Functor.Final.isColimitWhiskerEquiv (principalIsoFanTargetIndex a b e i)
    (principalAlgebraCocone R (B i) (b i))).symm (principalAlgebraIsColimit R (B i) (b i))

/-- All finite coordinate equivalences commute with transition maps. -/
def principalIsoFanRingIso (i : ι) :
    principalIsoFanSourceDiagram a b e i ≅ principalIsoFanTargetDiagram a b e i :=
  NatIso.ofComponents (fun x ↦
    (principalFanStageEquiv a b e x i).toRingEquiv.toCommRingCatIso) (by
      intro x y h
      apply CommRingCat.hom_ext
      exact congrArg AlgHom.toRingHom (principalFan_hom_comm (leOfHom h) i))

/-- Projections from the original full source scheme. -/
def principalIsoFanChartCone : Cone ((principalIsoFanChartDiagram a b e).op ⋙ Scheme.Spec) :=
  Scheme.Spec.mapCone (principalIsoFanChartCocone a b e).op

/-- Projections from an original source principal-open scheme. -/
def principalIsoFanSourceCone (i : ι) :
    Cone ((principalIsoFanSourceDiagram a b e i).op ⋙ Scheme.Spec) :=
  Scheme.Spec.mapCone (principalIsoFanSourceCocone a b e i).op

/-- Projections from an original target principal-open scheme. -/
def principalIsoFanTargetCone (i : ι) :
    Cone ((principalIsoFanTargetDiagram a b e i).op ⋙ Scheme.Spec) :=
  Scheme.Spec.mapCone (principalIsoFanTargetCocone a b e i).op

/-- The one ambient chart is the inverse limit of all shared isomorphism stages. -/
def principalIsoFanChartIsLimit : IsLimit (principalIsoFanChartCone a b e) :=
  isLimitOfPreserves Scheme.Spec (principalIsoFanChartIsColimit a b e).op

/-- Distinct source opens are recovered over one ambient chart system. -/
def principalIsoFanSourceIsLimit (i : ι) : IsLimit (principalIsoFanSourceCone a b e i) :=
  isLimitOfPreserves Scheme.Spec (principalIsoFanSourceIsColimit a b e i).op

/-- The target schemes are recovered on the same system. -/
def principalIsoFanTargetIsLimit (i : ι) : IsLimit (principalIsoFanTargetCone a b e i) :=
  isLimitOfPreserves Scheme.Spec (principalIsoFanTargetIsColimit a b e i).op

/-- Actual natural isomorphisms of the principal-open inverse systems. -/
def principalIsoFanSchemeIso (i : ι) :
    (principalIsoFanTargetDiagram a b e i).op ⋙ Scheme.Spec ≅
      (principalIsoFanSourceDiagram a b e i).op ⋙ Scheme.Spec :=
  Functor.isoWhiskerRight (NatIso.op (principalIsoFanRingIso a b e i)) Scheme.Spec

omit [Finite ι] in
/-- The natural coordinate isomorphisms recover the prescribed original isomorphisms. -/
theorem principalIsoFanRingIso_fac (i : ι) (x : PrincipalFanIsomorphismStage a b e) :
    (principalIsoFanRingIso a b e i).hom.app x ≫
        (principalIsoFanTargetCocone a b e i).ι.app x =
      (principalIsoFanSourceCocone a b e i).ι.app x ≫
        CommRingCat.ofHom (e i).toAlgHom.toRingHom := by
  apply CommRingCat.hom_ext
  exact congrArg AlgHom.toRingHom (x.val.fac i)

end FLT.Mazur.FiniteTypeRelationModel
