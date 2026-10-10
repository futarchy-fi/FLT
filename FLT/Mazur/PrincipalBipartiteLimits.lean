/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PrincipalBipartiteCofinal
public import FLT.Mazur.FiniteTypePrincipalApproximation

/-!
# Recovering charts and overlaps from one incidence index

All chart and overlap models use one filtered index, with a single model for
every occurrence of a chart. Every incidence map recovers its original map.
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry

namespace FLT.Mazur.FiniteTypeRelationModel

universe u v w z

variable {R : Type u} [CommRing R] {ι : Type v} {κ : Type w} {E : κ → Type z}
  [∀ j, Finite (E j)]
  {A : ι → Type u} [∀ i, CommRing (A i)] [∀ i, Algebra R (A i)]
  [∀ i, Algebra.FiniteType R (A i)]
  {B : κ → Type u} [∀ j, CommRing (B j)] [∀ j, Algebra R (B j)]
  [∀ j, Algebra.FiniteType R (B j)]
  (src : ∀ j, E j → ι) (a : ∀ i, A i) (b : ∀ j, B j)
  (f : ∀ j e, Localization.Away (a (src j e)) →ₐ[R] Localization.Away (b j))

/-- Source principal rings indexed by compatible coordinate lifts. -/
def principalBipartiteSourceDiagram (i : ι) : PrincipalBipartiteStage src a b f ⥤ CommRingCat.{u} :=
  principalBipartiteSourceIndex src a b f i ⋙ FiniteRelationLocalization.ringDiagram R
    (relationIdeal R (A i)) (principalRepresentative R (A i) (a i))

/-- Target principal rings indexed by compatible coordinate lifts. -/
def principalBipartiteTargetDiagram (j : κ) : PrincipalBipartiteStage src a b f ⥤ CommRingCat.{u} :=
  principalBipartiteTargetIndex src a b f j ⋙ FiniteRelationLocalization.ringDiagram R
    (relationIdeal R (B j)) (principalRepresentative R (B j) (b j))

/-- The finite coordinate maps commute with every refinement. -/
def principalBipartiteRingMap (j : κ) (e : E j) :
    principalBipartiteSourceDiagram src a b f (src j e) ⟶
      principalBipartiteTargetDiagram src a b f j where
  app x := CommRingCat.ofHom (x.hom j e).toRingHom
  naturality x y h := by
    apply CommRingCat.hom_ext
    exact congrArg AlgHom.toRingHom (principalBipartite_hom_comm (leOfHom h) j e)

/-- The original source principal ring receives the compatible source projections. -/
def principalBipartiteSourceCocone (i : ι) : Cocone (principalBipartiteSourceDiagram src a b f i) :=
  (principalAlgebraCocone R (A i) (a i)).whisker (principalBipartiteSourceIndex src a b f i)

/-- The original target principal ring receives the compatible target projections. -/
def principalBipartiteTargetCocone (j : κ) : Cocone (principalBipartiteTargetDiagram src a b f j) :=
  (principalAlgebraCocone R (B j) (b j)).whisker (principalBipartiteTargetIndex src a b f j)

/-- Cofinality recovers the original source ring on the shared coordinate index. -/
def principalBipartiteSourceIsColimit (i : ι) :
    IsColimit (principalBipartiteSourceCocone src a b f i) :=
  (Functor.Final.isColimitWhiskerEquiv (principalBipartiteSourceIndex src a b f i)
    (principalAlgebraCocone R (A i) (a i))).symm (principalAlgebraIsColimit R (A i) (a i))

/-- Cofinality recovers the original target ring on the shared coordinate index. -/
def principalBipartiteTargetIsColimit (j : κ) :
    IsColimit (principalBipartiteTargetCocone src a b f j) :=
  (Functor.Final.isColimitWhiskerEquiv (principalBipartiteTargetIndex src a b f j)
    (principalAlgebraCocone R (B j) (b j))).symm (principalAlgebraIsColimit R (B j) (b j))

omit [∀ j, Finite (E j)] in
/-- The natural transformation recovers the original map on colimit projections. -/
theorem principalBipartiteRingMap_fac (j : κ) (e : E j) (x : PrincipalBipartiteStage src a b f) :
    (principalBipartiteRingMap src a b f j e).app x ≫
        (principalBipartiteTargetCocone src a b f j).ι.app x =
      (principalBipartiteSourceCocone src a b f (src j e)).ι.app x ≫
        CommRingCat.ofHom (f j e).toRingHom := by
  apply CommRingCat.hom_ext
  exact congrArg AlgHom.toRingHom (x.fac j e)

/-- The actual source principal-open scheme is the vertex of the reindexed cone. -/
def principalBipartiteSourceCone (i : ι) :
    Cone ((principalBipartiteSourceDiagram src a b f i).op ⋙ Scheme.Spec) :=
  Scheme.Spec.mapCone (principalBipartiteSourceCocone src a b f i).op

/-- The actual target principal-open scheme is the vertex of the reindexed cone. -/
def principalBipartiteTargetCone (j : κ) :
    Cone ((principalBipartiteTargetDiagram src a b f j).op ⋙ Scheme.Spec) :=
  Scheme.Spec.mapCone (principalBipartiteTargetCocone src a b f j).op

/-- The source principal open is the inverse limit over compatible coordinate models. -/
def principalBipartiteSourceIsLimit (i : ι) : IsLimit (principalBipartiteSourceCone src a b f i) :=
  isLimitOfPreserves Scheme.Spec (principalBipartiteSourceIsColimit src a b f i).op

/-- The target principal open is the inverse limit over compatible coordinate models. -/
def principalBipartiteTargetIsLimit (j : κ) : IsLimit (principalBipartiteTargetCone src a b f j) :=
  isLimitOfPreserves Scheme.Spec (principalBipartiteTargetIsColimit src a b f j).op

/-- Coordinate maps of affine schemes form a natural transformation of inverse systems. -/
def principalBipartiteSchemeMap (j : κ) (e : E j) :
    (principalBipartiteTargetDiagram src a b f j).op ⋙ Scheme.Spec ⟶
      (principalBipartiteSourceDiagram src a b f (src j e)).op ⋙ Scheme.Spec :=
  Functor.whiskerRight (NatTrans.op (principalBipartiteRingMap src a b f j e)) Scheme.Spec

omit [∀ j, Finite (E j)] in
/-- Every finite coordinate map is compatible with the original scheme morphism. -/
theorem principalBipartiteSchemeMap_fac (j : κ) (e : E j) (x : PrincipalBipartiteStage src a b f) :
    Spec.map (CommRingCat.ofHom (f j e).toRingHom) ≫
        (principalBipartiteSourceCone src a b f (src j e)).π.app (.op x) =
      (principalBipartiteTargetCone src a b f j).π.app (.op x) ≫
        (principalBipartiteSchemeMap src a b f j e).app (.op x) := by
  change Spec.map (CommRingCat.ofHom (f j e).toRingHom) ≫
      Spec.map (CommRingCat.ofHom
        (principalStageMap R (A (src j e)) (a (src j e)) (x.source (src j e))).toRingHom) =
    Spec.map (CommRingCat.ofHom (principalStageMap R (B j) (b j) (x.target j)).toRingHom) ≫
      Spec.map (CommRingCat.ofHom (x.hom j e).toRingHom)
  simp only [← Spec.map_comp]
  congr 1
  exact CommRingCat.hom_ext (congrArg AlgHom.toRingHom (x.fac j e).symm)

end FLT.Mazur.FiniteTypeRelationModel
