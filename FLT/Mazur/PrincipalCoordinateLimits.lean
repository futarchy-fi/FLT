/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PrincipalCoordinateCofinal
public import FLT.Mazur.FiniteTypePrincipalApproximation

/-!
# Recovering a coordinate map from a compatible system of principal models

Both charts use the same filtered index of commuting lifts. Their colimit
rings and inverse-limit schemes are the original principal opens, and the
finite coordinate maps are a natural transformation compatible with the
original coordinate map.
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry

namespace FLT.Mazur.FiniteTypeRelationModel

universe u

variable {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra R B] [Algebra.FiniteType R A] [Algebra.FiniteType R B]
  (a : A) (b : B) (f : Localization.Away a →ₐ[R] Localization.Away b)

/-- Source principal rings indexed by compatible coordinate lifts. -/
def principalCoordinateSourceDiagram : PrincipalMapStage a b f ⥤ CommRingCat.{u} :=
  principalSourceIndex a b f ⋙ FiniteRelationLocalization.ringDiagram R
    (relationIdeal R A) (principalRepresentative R A a)

/-- Target principal rings indexed by compatible coordinate lifts. -/
def principalCoordinateTargetDiagram : PrincipalMapStage a b f ⥤ CommRingCat.{u} :=
  principalTargetIndex a b f ⋙ FiniteRelationLocalization.ringDiagram R
    (relationIdeal R B) (principalRepresentative R B b)

/-- The finite coordinate maps commute with every refinement. -/
def principalCoordinateRingMap :
    principalCoordinateSourceDiagram a b f ⟶ principalCoordinateTargetDiagram a b f where
  app x := CommRingCat.ofHom x.hom.toRingHom
  naturality x y h := by
    apply CommRingCat.hom_ext
    exact congrArg AlgHom.toRingHom (leOfHom h).choose_spec.choose_spec

/-- The original source principal ring receives the compatible source projections. -/
def principalCoordinateSourceCocone : Cocone (principalCoordinateSourceDiagram a b f) :=
  (principalAlgebraCocone R A a).whisker (principalSourceIndex a b f)

/-- The original target principal ring receives the compatible target projections. -/
def principalCoordinateTargetCocone : Cocone (principalCoordinateTargetDiagram a b f) :=
  (principalAlgebraCocone R B b).whisker (principalTargetIndex a b f)

/-- Cofinality recovers the original source ring on the shared coordinate index. -/
def principalCoordinateSourceIsColimit : IsColimit (principalCoordinateSourceCocone a b f) :=
  (Functor.Final.isColimitWhiskerEquiv (principalSourceIndex a b f)
    (principalAlgebraCocone R A a)).symm (principalAlgebraIsColimit R A a)

/-- Cofinality recovers the original target ring on the shared coordinate index. -/
def principalCoordinateTargetIsColimit : IsColimit (principalCoordinateTargetCocone a b f) :=
  (Functor.Final.isColimitWhiskerEquiv (principalTargetIndex a b f)
    (principalAlgebraCocone R B b)).symm (principalAlgebraIsColimit R B b)

/-- The natural transformation recovers the original map on colimit projections. -/
theorem principalCoordinateRingMap_fac (x : PrincipalMapStage a b f) :
    (principalCoordinateRingMap a b f).app x ≫
        (principalCoordinateTargetCocone a b f).ι.app x =
      (principalCoordinateSourceCocone a b f).ι.app x ≫ CommRingCat.ofHom f.toRingHom := by
  apply CommRingCat.hom_ext
  exact congrArg AlgHom.toRingHom x.fac

/-- The actual source principal-open scheme is the vertex of the reindexed cone. -/
def principalCoordinateSourceCone :
    Cone ((principalCoordinateSourceDiagram a b f).op ⋙ Scheme.Spec) :=
  Scheme.Spec.mapCone (principalCoordinateSourceCocone a b f).op

/-- The actual target principal-open scheme is the vertex of the reindexed cone. -/
def principalCoordinateTargetCone :
    Cone ((principalCoordinateTargetDiagram a b f).op ⋙ Scheme.Spec) :=
  Scheme.Spec.mapCone (principalCoordinateTargetCocone a b f).op

/-- The source principal open is the inverse limit over compatible coordinate models. -/
def principalCoordinateSourceIsLimit : IsLimit (principalCoordinateSourceCone a b f) :=
  isLimitOfPreserves Scheme.Spec (principalCoordinateSourceIsColimit a b f).op

/-- The target principal open is the inverse limit over compatible coordinate models. -/
def principalCoordinateTargetIsLimit : IsLimit (principalCoordinateTargetCone a b f) :=
  isLimitOfPreserves Scheme.Spec (principalCoordinateTargetIsColimit a b f).op

/-- Coordinate maps of affine schemes form a natural transformation of inverse systems. -/
def principalCoordinateSchemeMap :
    (principalCoordinateTargetDiagram a b f).op ⋙ Scheme.Spec ⟶
      (principalCoordinateSourceDiagram a b f).op ⋙ Scheme.Spec :=
  Functor.whiskerRight (NatTrans.op (principalCoordinateRingMap a b f)) Scheme.Spec

/-- Every finite coordinate map is compatible with the original scheme morphism. -/
theorem principalCoordinateSchemeMap_fac (x : PrincipalMapStage a b f) :
    Spec.map (CommRingCat.ofHom f.toRingHom) ≫
        (principalCoordinateSourceCone a b f).π.app (.op x) =
      (principalCoordinateTargetCone a b f).π.app (.op x) ≫
        (principalCoordinateSchemeMap a b f).app (.op x) := by
  change Spec.map (CommRingCat.ofHom f.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (principalStageMap R A a x.source).toRingHom) =
    Spec.map (CommRingCat.ofHom (principalStageMap R B b x.target).toRingHom) ≫
      Spec.map (CommRingCat.ofHom x.hom.toRingHom)
  simp only [← Spec.map_comp]
  congr 1
  exact CommRingCat.hom_ext (congrArg AlgHom.toRingHom x.fac.symm)

end FLT.Mazur.FiniteTypeRelationModel
