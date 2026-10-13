/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteSmoothCyclicMarking
public import FLT.Mazur.PolygonCompleteCartesianRotation

/-!
# Cyclic rotations of the actual complete-family smooth locus

The original whole-family rotations preserve the actual smooth open on every
cartesian square. Their restrictions satisfy the group action laws and carry
the original smooth markings to their cyclically shifted labels.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.PolygonInfinitesimalStages
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase completeRotation
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]
  {S Y : Scheme} (s : S ⟶ Spec (.of (PowerSeries K)))
  (p : Y ⟶ exactVeroneseProj K n h) (q : Y ⟶ S)
  (hs : IsPullback p q (exactVeroneseProjToBase K n h) s)

variable [LocallyOfFinitePresentation q]

/-- The actual whole-family rotation preserves its relative smooth open. -/
theorem completeCartesianRotation_preimage_smoothLocus (a : ZMod n) :
    completeCartesianRotation K n h s p q hs a ⁻¹ᵁ q.smoothLocus = q.smoothLocus := by
  let _ : IsIso (completeCartesianRotation K n h s p q hs a) :=
    (completeCartesianRotationIso K n h s p q hs a).isIso_hom
  rw [Scheme.Hom.preimage_smoothLocus_eq]
  congr 1
  exact completeCartesianRotation_snd K n h s p q hs a

/-- Restriction of the original complete-family rotation to the actual smooth open. -/
def completeSmoothCartesianRotation (a : ZMod n) :
    (q.smoothLocus : Scheme) ⟶ q.smoothLocus := by
  refine IsOpenImmersion.lift q.smoothLocus.ι
    (q.smoothLocus.ι ≫ completeCartesianRotation K n h s p q hs a) ?_
  rw [Scheme.Opens.range_ι]
  rintro _ ⟨x, rfl⟩
  have he := congrArg (fun U : Y.Opens ↦ x.1 ∈ U)
    (completeCartesianRotation_preimage_smoothLocus K n h s p q hs a)
  exact he.mpr x.2

/-- Restriction retains the original whole-family automorphism. -/
@[reassoc] theorem completeSmoothCartesianRotation_ι (a : ZMod n) :
    completeSmoothCartesianRotation K n h s p q hs a ≫ q.smoothLocus.ι =
      q.smoothLocus.ι ≫ completeCartesianRotation K n h s p q hs a := by
  exact IsOpenImmersion.lift_fac _ _ _

/-- The restricted rotation is over the specified original base. -/
@[reassoc] theorem completeSmoothCartesianRotation_toBase (a : ZMod n) :
    completeSmoothCartesianRotation K n h s p q hs a ≫ q.smoothLocus.ι ≫ q =
      q.smoothLocus.ι ≫ q := by
  rw [completeSmoothCartesianRotation_ι_assoc, completeCartesianRotation_snd]

/-- The identity label acts trivially on the actual smooth open. -/
@[simp] theorem completeSmoothCartesianRotation_zero :
    completeSmoothCartesianRotation K n h s p q hs 0 = 𝟙 _ := by
  apply (cancel_mono q.smoothLocus.ι).mp
  rw [completeSmoothCartesianRotation_ι, completeCartesianRotation_zero,
    Category.comp_id, Category.id_comp]

/-- Cyclic addition is composition on the actual smooth open. -/
theorem completeSmoothCartesianRotation_add (a b : ZMod n) :
    completeSmoothCartesianRotation K n h s p q hs (a + b) =
      completeSmoothCartesianRotation K n h s p q hs a ≫
        completeSmoothCartesianRotation K n h s p q hs b := by
  apply (cancel_mono q.smoothLocus.ι).mp
  simp only [Category.assoc, completeSmoothCartesianRotation_ι,
    completeSmoothCartesianRotation_ι_assoc, completeCartesianRotation_add]

/-- Negative rotation gives an actual inverse on the smooth open. -/
def completeSmoothCartesianRotationIso (a : ZMod n) :
    (q.smoothLocus : Scheme) ≅ q.smoothLocus := by
  exact
    { hom := completeSmoothCartesianRotation K n h s p q hs a
      inv := completeSmoothCartesianRotation K n h s p q hs (-a)
      hom_inv_id := by rw [← completeSmoothCartesianRotation_add, add_neg_cancel,
        completeSmoothCartesianRotation_zero]
      inv_hom_id := by rw [← completeSmoothCartesianRotation_add, neg_add_cancel,
        completeSmoothCartesianRotation_zero] }

/-- Smooth rotation carries the exact original marking to its cyclic successor. -/
@[reassoc] theorem completeSmoothCartesianMarking_rotation (a : ZMod n) (i : Fin n) :
    completeSmoothCartesianMarking K n h s p q hs i ≫
      completeSmoothCartesianRotation K n h s p q hs a =
        completeSmoothCartesianMarking K n h s p q hs (PolygonPinching.rotateIndex a i) := by
  apply (cancel_mono q.smoothLocus.ι).mp
  rw [Category.assoc, completeSmoothCartesianRotation_ι,
    completeSmoothCartesianMarking_ι_assoc, completeSmoothCartesianMarking_ι,
    completeCartesianMarking_rotation]

end FLT.Mazur.PolygonInfinitesimalStages
