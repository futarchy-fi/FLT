/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteBoundaryTestDivisor
public import FLT.Mazur.PolygonCompleteCyclicBoundaryParameters
public import FLT.Mazur.PolygonCompleteClosedCyclicAction
public import FLT.Mazur.PolygonParameterMarkingOriginal

/-!
# Cyclic translations preserve the original complete boundary subgroup divisor

For the tests constructed from the complete subgroup, each cyclic translation
is an original all-one rotation. The full moved product is therefore the same
original subgroup ideal, including over nonreduced parameter schemes.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory MonObj
namespace FLT.Mazur.PolygonInfinitesimalStages
open PolygonUniversalAction CyclicBoundaryParameter PolygonParameterTranslation PolygonPinching
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase translationIso
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]
  {T : Scheme} (g : T ⟶ Spec (.of K))
  (a : UniversalWeierstrass.Labels 4 →* (Over.mk g ⟶ G K n))
  (b : UniversalWeierstrass.Labels 3 →* (Over.mk g ⟶ G K n))
local notation "p" => PolygonCyclicAtlas.normalization K n h
local notation "q" => PolygonCyclicAtlas.nodes K n h
local notation "hn" => (Nat.lt_of_lt_of_le (Nat.succ_pos 1) h)
local notation "hp" => PolygonCyclicPushout.isPushout K n h hn
local notation "f" => completeBoundaryTestParameter K n h g a b
local notation "c" => fun j : Multiplicative (ZMod n) ↦
  markedSection (G K n) n g (f) (1, 1, j)

/-- Each actual subgroup label is the original all-one rotation parameter. -/
theorem completeBoundaryTestParameter_original (j : Multiplicative (ZMod n)) :
    c j = originalParameter K n g 1 j.toAdd := by
  dsimp only
  rw [completeBoundaryTestParameter_section, completeClosedBoundaryMarking_eq,
    ConstantCyclicInclusion.component_inclusion, ← completeClosedGroupPoint_eq]
  rfl

/-- Cyclic translation permutes every factor of the original complete subgroup product. -/
theorem completeBoundaryTestParameter_movedProduct (j : Multiplicative (ZMod n)) :
    movedProductMarkingIdeal K n hn p q hp g (c j) (fun _ ↦ 1) =
      productMarkingIdeal K n p g (fun _ ↦ 1) := by
  rw [completeBoundaryTestParameter_original, movedProductMarkingIdeal]
  simp only [movedMarkingIdeal_originalParameter, _root_.one_mul]
  have hb : Function.Bijective (rotateIndex j.toAdd : Fin n → Fin n) := by
    refine Function.bijective_iff_has_inverse.mpr ⟨rotateIndex (-j.toAdd), ?_, ?_⟩
    · intro i
      rw [← rotateIndex_add, add_neg_cancel, rotateIndex_zero]
    · intro i
      rw [← rotateIndex_add, neg_add_cancel, rotateIndex_zero]
  exact Equiv.prod_comp (Equiv.ofBijective (rotateIndex j.toAdd) hb)
    (fun i ↦ PolygonMarkingBaseChange.markingIdeal K n p g 1 i)

/-- The actual complete fiber comparison retains the original subgroup ideal after rotation. -/
theorem completeBoundaryTestComparison_subgroup (j : Multiplicative (ZMod n)) :
    (∏ i : Fin n,
      (completeFiberMarking K n h (g ≫ completeClosedBase K) i).ker).comap
        (completeCyclicBoundaryComparison K n h g (f) j).hom =
          ((completeClosedFiniteSubgroup K n h).baseChange g).ideal := by
  rw [completeCyclicBoundaryComparison_marking, completeBoundaryTestParameter_movedProduct,
    completeBoundarySubgroup_product]

end FLT.Mazur.PolygonInfinitesimalStages
