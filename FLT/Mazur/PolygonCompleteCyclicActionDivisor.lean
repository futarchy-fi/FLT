/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteWholeActionCyclic
public import FLT.Mazur.PolygonCompleteDivisorLine
public import FLT.Mazur.SectionCartesianKernel

/-!
# The cyclic whole action retains the original marking divisor

The actual cyclic action maps form Cartesian squares over the original base.
They preserve the full product of original marking ideals and all its powers.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.PolygonInfinitesimalStages
open FCurve PolygonPinching
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase completeRotation
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]
local notation "π" => exactVeroneseProjToBase K n h

/-- The cyclic section acts on the unchanged whole scheme by the constructed full action. -/
def completeCyclicActionMap (b : ZMod n) : exactVeroneseProj K n h ⟶
    exactVeroneseProj K n h :=
  (completeWholeTranslation K n h (completeOriginalSmoothCyclicPoint K n h b)).left

/-- The original whole-family rotation is recovered exactly. -/
theorem completeCyclicActionMap_rotation (b : ZMod n) :
    completeCyclicActionMap K n h b = completeRotation K n h b := by
  exact congrArg Over.Hom.left (completeWholeTranslation_cyclic K n h b)

/-- Every cyclic action map is an actual automorphism. -/
instance completeCyclicActionMap_isIso (b : ZMod n) :
    IsIso (completeCyclicActionMap K n h b) := by
  rw [completeCyclicActionMap_rotation]
  simpa only [completeRotation] using (completeRotationIso K n h b).isIso_hom

/-- The zero cyclic label acts as the identity of the original whole scheme. -/
theorem completeCyclicActionMap_zero : completeCyclicActionMap K n h 0 = 𝟙 _ := by
  rw [completeCyclicActionMap_rotation, completeRotation_zero]

/-- Successive cyclic action maps retain the original addition of labels. -/
theorem completeCyclicActionMap_add (b c : ZMod n) :
    completeCyclicActionMap K n h b ≫ completeCyclicActionMap K n h c =
      completeCyclicActionMap K n h (b + c) := by
  simp only [completeCyclicActionMap_rotation, ← completeRotation_add]

/-- The cyclic action forms a Cartesian square over the identity of the original base. -/
theorem completeCyclicActionMap_isPullback (b : ZMod n) :
    IsPullback (completeCyclicActionMap K n h b) (π) (π) (𝟙 _) := by
  apply IsPullback.of_horiz_isIso
  constructor
  rw [completeCyclicActionMap_rotation, completeRotation_toBase, Category.comp_id]

/-- The cyclic whole action preserves the full original product-marking ideal. -/
theorem completeCyclicActionMap_divisor (b : ZMod n) :
    (completeMarkingDivisor K n h).comap (completeCyclicActionMap K n h b) =
      completeMarkingDivisor K n h := by
  let _ := exactVeroneseProjToBase_isProper K n h
  have hp := section_prod_comap_of_cartesian (completeCyclicActionMap_isPullback K n h b)
    Finset.univ (completeBaseMarking K n h)
    (fun i ↦ completeBaseMarking K n h (rotateIndex b i))
    (completeBaseMarking_toBase K n h)
    (fun i ↦ completeBaseMarking_toBase K n h (rotateIndex b i))
    (fun i ↦ by rw [Category.id_comp]; exact completeWholeTranslation_cyclic_marking K n h b i)
  have hb : Function.Bijective (rotateIndex b : Fin n → Fin n) := by
    refine Function.bijective_iff_has_inverse.mpr ⟨rotateIndex (-b), ?_, ?_⟩
    · intro i
      rw [← rotateIndex_add, add_neg_cancel, rotateIndex_zero]
    · intro i
      rw [← rotateIndex_add, neg_add_cancel, rotateIndex_zero]
  change (∏ i, (completeBaseMarking K n h i).ker).comap _ = _
  rw [← Equiv.prod_comp (Equiv.ofBijective (rotateIndex b) hb)]
  exact hp

/-- Every multiplicity of the original marked divisor is preserved. -/
theorem completeCyclicActionMap_divisor_power (b : ZMod n) (d : ℕ) :
    (completeMarkingDivisor K n h ^ d).comap (completeCyclicActionMap K n h b) =
      completeMarkingDivisor K n h ^ d := by
  rw [idealSheaf_comap_pow, completeCyclicActionMap_divisor]

end FLT.Mazur.PolygonInfinitesimalStages
