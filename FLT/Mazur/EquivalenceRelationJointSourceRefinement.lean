/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EquivalenceRelationJointFrameCover
public import FLT.Mazur.SchemeEffectiveEpiSections

/-!
# Exhaustive common-frame comparisons after arbitrary source refinement

Base change of the constructed finite etale comparison covers every scheme test,
including open domains, original closed boundaries and infinitesimal thickenings.
It detects original coefficient identities without any completeness condition.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationNormalizedFrames.MixedFrames
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D A : Scheme.{0}} {p q : D ⟶ A} [IsSeparated p] [Etale p]
  (e : CategoryTheory.EquivalenceRelation p q)
  {I J : Type} [Fintype I] [Fintype J] (o : I) (o' : J)
  {T : Scheme.{0}} (z : T ⟶ relation p q I J o o')

/-- Pull back the whole comparison, retaining every original common-frame component. -/
def jointTestSource : Scheme := pullback (jointComparison e o o') z

/-- The full source comparison over an arbitrary original test. -/
def jointTestMap : jointTestSource e o o' z ⟶ T := pullback.snd _ _

instance jointTestMap_etale : Etale (jointTestMap e o o' z) := by
  unfold jointTestMap
  infer_instance

instance jointTestMap_surjective : Surjective (jointTestMap e o o' z) := by
  unfold jointTestMap
  infer_instance

instance jointTestMap_epi : Epi (jointTestMap e o o' z) :=
  AlgebraicGeometry.Flat.epi_of_flat_of_surjective _

omit [Etale p] in
/-- The pulled comparison still maps to the unchanged original mixed relation. -/
@[reassoc] theorem jointTestMap_original :
    jointTestMap e o o' z ≫ z =
      pullback.fst (jointComparison e o o') z ≫ jointComparison e o o' :=
  pullback.condition.symm

omit [Etale p] in
/-- In particular the entire original arrow is retained on all infinitesimal tests. -/
@[reassoc] theorem jointTestMap_arrow :
    jointTestMap e o o' z ≫ z ≫ arrow p q I J o o' =
      pullback.fst (jointComparison e o o') z ≫
        jointComparison e o o' ≫ arrow p q I J o o' := by
  rw [← Category.assoc, jointTestMap_original, Category.assoc]

/-- Original regular functions are detected on the constructed exhaustive source comparison. -/
theorem jointTestMap_appTop_injective : Function.Injective (jointTestMap e o o' z).appTop :=
  SchemeEffectiveEpiSections.appTop_injective _

/-- Equality of original coefficients is equivalent to equality on the exhaustive comparison. -/
theorem jointTestMap_coefficients_iff (a b : Γ(T, ⊤)) :
    (jointTestMap e o o' z).appTop a = (jointTestMap e o o' z).appTop b ↔ a = b :=
  (jointTestMap_appTop_injective e o o' z).eq_iff

/-- A finite coefficient identity descends from this actual cover of the whole original test. -/
theorem jointTestMap_finite_identity_iff {L : Type} (s : Finset L) (a b : L → Γ(T, ⊤)) :
    (∑ l ∈ s, a l * b l) = 1 ↔
      (∑ l ∈ s, (jointTestMap e o o' z).appTop (a l) *
        (jointTestMap e o o' z).appTop (b l)) = 1 := by
  rw [← (jointTestMap_appTop_injective e o o' z).eq_iff]
  simp only [map_sum, map_mul, map_one]

/-- Every independent refinement maps to the previous comparison by the actual pullback map. -/
def jointTestRefine {T' : Scheme.{0}} (a : T' ⟶ T) :
    jointTestSource e o o' (a ≫ z) ⟶ jointTestSource e o o' z :=
  pullback.lift (pullback.fst _ _) (jointTestMap e o o' (a ≫ z) ≫ a) (by
    rw [Category.assoc, jointTestMap_original])

omit [Etale p] in
/-- Refinement commutes with the original source projection on the entire scheme. -/
@[reassoc] theorem jointTestRefine_map {T' : Scheme.{0}} (a : T' ⟶ T) :
    jointTestRefine e o o' z a ≫ jointTestMap e o o' z =
      jointTestMap e o o' (a ≫ z) ≫ a := pullback.lift_snd _ _ _

omit [Etale p] in
/-- Refinement retains the identical common-frame component in the total comparison. -/
@[reassoc] theorem jointTestRefine_fst {T' : Scheme.{0}} (a : T' ⟶ T) :
    jointTestRefine e o o' z a ≫ pullback.fst (jointComparison e o o') z =
      pullback.fst (jointComparison e o o') (a ≫ z) := pullback.lift_fst _ _ _

omit [Etale p] in
/-- These two retained projections determine the refinement map uniquely. -/
theorem jointTestRefine_unique {T' : Scheme.{0}} (a : T' ⟶ T)
    (w : jointTestSource e o o' (a ≫ z) ⟶ jointTestSource e o o' z)
    (hf : w ≫ pullback.fst (jointComparison e o o') z =
      pullback.fst (jointComparison e o o') (a ≫ z))
    (hs : w ≫ jointTestMap e o o' z = jointTestMap e o o' (a ≫ z) ≫ a) :
    w = jointTestRefine e o o' z a := by
  apply pullback.hom_ext
  · exact hf.trans (jointTestRefine_fst e o o' z a).symm
  · exact hs.trans (jointTestRefine_map e o o' z a).symm

end FLT.Mazur.EquivalenceRelationNormalizedFrames.MixedFrames
