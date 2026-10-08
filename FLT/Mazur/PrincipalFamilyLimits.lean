/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PrincipalFamilyCofinal
public import FLT.Mazur.FiniteTypePrincipalApproximation

/-!
# Recovering a finite coordinate family from its common index

All source charts and the common target use one filtered index. Each original
principal open is its inverse limit, and all incoming maps are recovered.
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry

namespace FLT.Mazur.FiniteTypeRelationModel

universe u v

variable {R : Type u} [CommRing R] {ι : Type v} [Finite ι]
  {A : ι → Type u} [∀ i, CommRing (A i)] [∀ i, Algebra R (A i)]
  [∀ i, Algebra.FiniteType R (A i)]
  {B : Type u} [CommRing B] [Algebra R B] [Algebra.FiniteType R B]
  (a : ∀ i, A i) (b : B)
  (f : ∀ i, Localization.Away (a i) →ₐ[R] Localization.Away b)

/-- Source principal rings indexed by compatible coordinate lifts. -/
def principalFamilySourceDiagram (i : ι) : PrincipalFamilyStage a b f ⥤ CommRingCat.{u} :=
  principalFamilySourceIndex a b f i ⋙ FiniteRelationLocalization.ringDiagram R
    (relationIdeal R (A i)) (principalRepresentative R (A i) (a i))

/-- Target principal rings indexed by compatible coordinate lifts. -/
def principalFamilyTargetDiagram : PrincipalFamilyStage a b f ⥤ CommRingCat.{u} :=
  principalFamilyTargetIndex a b f ⋙ FiniteRelationLocalization.ringDiagram R
    (relationIdeal R B) (principalRepresentative R B b)

/-- The finite coordinate maps commute with every refinement. -/
def principalFamilyRingMap (i : ι) :
    principalFamilySourceDiagram a b f i ⟶ principalFamilyTargetDiagram a b f where
  app x := CommRingCat.ofHom (x.hom i).toRingHom
  naturality x y h := by
    apply CommRingCat.hom_ext
    exact congrArg AlgHom.toRingHom ((leOfHom h).choose_spec.choose_spec i)

/-- The original source principal ring receives the compatible source projections. -/
def principalFamilySourceCocone (i : ι) : Cocone (principalFamilySourceDiagram a b f i) :=
  (principalAlgebraCocone R (A i) (a i)).whisker (principalFamilySourceIndex a b f i)

/-- The original target principal ring receives the compatible target projections. -/
def principalFamilyTargetCocone : Cocone (principalFamilyTargetDiagram a b f) :=
  (principalAlgebraCocone R B b).whisker (principalFamilyTargetIndex a b f)

/-- Cofinality recovers the original source ring on the shared coordinate index. -/
def principalFamilySourceIsColimit (i : ι) : IsColimit (principalFamilySourceCocone a b f i) :=
  (Functor.Final.isColimitWhiskerEquiv (principalFamilySourceIndex a b f i)
    (principalAlgebraCocone R (A i) (a i))).symm (principalAlgebraIsColimit R (A i) (a i))

/-- Cofinality recovers the original target ring on the shared coordinate index. -/
def principalFamilyTargetIsColimit : IsColimit (principalFamilyTargetCocone a b f) :=
  (Functor.Final.isColimitWhiskerEquiv (principalFamilyTargetIndex a b f)
    (principalAlgebraCocone R B b)).symm (principalAlgebraIsColimit R B b)

omit [Finite ι] in
/-- The natural transformation recovers the original map on colimit projections. -/
theorem principalFamilyRingMap_fac (i : ι) (x : PrincipalFamilyStage a b f) :
    (principalFamilyRingMap a b f i).app x ≫
        (principalFamilyTargetCocone a b f).ι.app x =
      (principalFamilySourceCocone a b f i).ι.app x ≫ CommRingCat.ofHom (f i).toRingHom := by
  apply CommRingCat.hom_ext
  exact congrArg AlgHom.toRingHom (x.fac i)

/-- The actual source principal-open scheme is the vertex of the reindexed cone. -/
def principalFamilySourceCone (i : ι) :
    Cone ((principalFamilySourceDiagram a b f i).op ⋙ Scheme.Spec) :=
  Scheme.Spec.mapCone (principalFamilySourceCocone a b f i).op

/-- The actual target principal-open scheme is the vertex of the reindexed cone. -/
def principalFamilyTargetCone :
    Cone ((principalFamilyTargetDiagram a b f).op ⋙ Scheme.Spec) :=
  Scheme.Spec.mapCone (principalFamilyTargetCocone a b f).op

/-- The source principal open is the inverse limit over compatible coordinate models. -/
def principalFamilySourceIsLimit (i : ι) : IsLimit (principalFamilySourceCone a b f i) :=
  isLimitOfPreserves Scheme.Spec (principalFamilySourceIsColimit a b f i).op

/-- The target principal open is the inverse limit over compatible coordinate models. -/
def principalFamilyTargetIsLimit : IsLimit (principalFamilyTargetCone a b f) :=
  isLimitOfPreserves Scheme.Spec (principalFamilyTargetIsColimit a b f).op

/-- Coordinate maps of affine schemes form a natural transformation of inverse systems. -/
def principalFamilySchemeMap (i : ι) :
    (principalFamilyTargetDiagram a b f).op ⋙ Scheme.Spec ⟶
      (principalFamilySourceDiagram a b f i).op ⋙ Scheme.Spec :=
  Functor.whiskerRight (NatTrans.op (principalFamilyRingMap a b f i)) Scheme.Spec

omit [Finite ι] in
/-- Every finite coordinate map is compatible with the original scheme morphism. -/
theorem principalFamilySchemeMap_fac (i : ι) (x : PrincipalFamilyStage a b f) :
    Spec.map (CommRingCat.ofHom (f i).toRingHom) ≫
        (principalFamilySourceCone a b f i).π.app (.op x) =
      (principalFamilyTargetCone a b f).π.app (.op x) ≫
        (principalFamilySchemeMap a b f i).app (.op x) := by
  change Spec.map (CommRingCat.ofHom (f i).toRingHom) ≫
      Spec.map (CommRingCat.ofHom (principalStageMap R (A i) (a i) (x.source i)).toRingHom) =
    Spec.map (CommRingCat.ofHom (principalStageMap R B b x.target).toRingHom) ≫
      Spec.map (CommRingCat.ofHom (x.hom i).toRingHom)
  simp only [← Spec.map_comp]
  congr 1
  exact CommRingCat.hom_ext (congrArg AlgHom.toRingHom (x.fac i).symm)

end FLT.Mazur.FiniteTypeRelationModel
