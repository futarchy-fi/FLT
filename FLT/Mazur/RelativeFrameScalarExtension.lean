/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RelativeCompleteFrameFiberIso

/-!
# Scalar extension of original frames and their coordinates

Every coordinate square is cartesian over an arbitrary morphism of field spectra.
Both fiber projections and the original coordinate morphisms are retained.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.RelativeOrderedTuples
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {S : Scheme.{0}} (E : Over S) [IsSeparated E.hom]
  (I : Type) [Fintype I] {K L : Type} [Field K] [Field L]
  {b : Spec (.of K) ⟶ S} (t : Over.mk b ⟶ distinctScheme E I)
  (g : Spec (.of L) ⟶ Spec (.of K))

/-- Scalar extension keeps the given original tuple map. -/
def scalarFrame : Over.mk (g ≫ b) ⟶ distinctScheme E I :=
  Over.homMk (g ≫ t.left) (by rw [Category.assoc, t.w]; rfl)

/-- The entire original fiber map under scalar extension. -/
def scalarFiberMap : pullback E.hom (g ≫ b) ⟶ pullback E.hom b :=
  pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ g)
    (by rw [Category.assoc, pullback.condition])

omit [IsSeparated E.hom] in
@[reassoc] theorem scalarFiberMap_fst :
    scalarFiberMap E g ≫ pullback.fst E.hom b = pullback.fst E.hom (g ≫ b) :=
  pullback.lift_fst _ _ _

omit [IsSeparated E.hom] in
@[reassoc] theorem scalarFiberMap_snd :
    scalarFiberMap E g ≫ pullback.snd E.hom b = pullback.snd E.hom (g ≫ b) ≫ g :=
  pullback.lift_snd _ _ _

omit [IsSeparated E.hom] in
/-- The comparison of the whole original fibers is cartesian. -/
theorem scalarFiberMap_isPullback :
    IsPullback (scalarFiberMap E g) (pullback.snd E.hom (g ≫ b))
      (pullback.snd E.hom b) g := by
  apply IsPullback.of_right (h₁₂ := pullback.fst E.hom b) (h₂₂ := b)
  · rw [scalarFiberMap_fst]
    exact IsPullback.of_hasPullback E.hom (g ≫ b)
  · exact scalarFiberMap_snd E g
  · exact IsPullback.of_hasPullback E.hom b

@[reassoc] theorem scalarFrame_geometric (i : I) :
    geometricCoordinate E I (scalarFrame E I t g) i ≫ scalarFiberMap E g =
      g ≫ geometricCoordinate E I t i := by
  apply pullback.hom_ext
  · simp only [Category.assoc, scalarFiberMap_fst, geometricCoordinate_fst]
    rfl
  · simp only [Category.assoc, scalarFiberMap_snd, geometricCoordinate_snd_assoc,
      geometricCoordinate_snd, Category.comp_id]

/-- Scalar extension of each original coordinate is its actual scheme pullback. -/
theorem scalarFrame_coordinate_isPullback (i : I) :
    IsPullback g (geometricCoordinate E I (scalarFrame E I t g) i)
      (geometricCoordinate E I t i) (scalarFiberMap E g) := by
  apply IsPullback.of_bot (v₂₁ := pullback.snd E.hom (g ≫ b))
    (v₂₂ := pullback.snd E.hom b)
  · simp only [geometricCoordinate_snd]
    exact IsPullback.of_id_snd
  · exact (scalarFrame_geometric E I t g i).symm
  · exact scalarFiberMap_isPullback E g

end FLT.Mazur.RelativeOrderedTuples
