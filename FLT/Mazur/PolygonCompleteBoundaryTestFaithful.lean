/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteBoundaryTestMarking
public import FLT.Mazur.CyclicBoundaryGroupSections

/-!
# Faithfulness of the original complete subgroup's boundary tests

The original complete closed sections are universally distinct. Every actual
boundary test retains this property after arbitrary parameter change, without
requiring the parameter scheme to be reduced or a field.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory MonObj
open scoped CategoryTheory.Obj
namespace FLT.Mazur.PolygonInfinitesimalStages
open PolygonUniversalAction CyclicBoundaryParameter GeneralizedEllipticCurve
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]
local notation "p" => PolygonCyclicAtlas.normalization K n h
local notation "q" => PolygonCyclicAtlas.nodes K n h
local notation "hn" => (Nat.lt_of_lt_of_le (Nat.succ_pos 1) h)
local notation "hp" => PolygonCyclicPushout.isPushout K n h hn
local notation "EC" => PolygonGeneralizedCurve.curve K n hn p q hp

/-- Original complete closed labels stay distinct on every nonempty test scheme. -/
theorem completeClosedBoundaryMarking_distinct :
    UniversallyDistinctSections.UniversallyDistinct
      (fun i : ZMod n ↦ completeClosedBoundaryMarking K n h (.ofAdd i)) := by
  intro V k hV i j hij
  let d := completeCyclicMarking K n h (completeClosedBase K)
    (completeClosedFiberInclusion K n h) (PolygonCyclicAtlas.toBase K n h)
    (completeClosedFiber_isPullback K n h)
  have he := congrArg (fun s ↦ s ≫ ConstantCyclicInclusion.retraction K n ≫ d) hij
  simp only [completeClosedBoundaryMarking_eq, Category.assoc,
    ConstantCyclicInclusion.inclusion_retraction_assoc, completeCyclicMarking_component,
    d] at he
  exact completeCyclicSection_universallyDistinct K n h (completeClosedBase K)
    (completeClosedFiberInclusion K n h) (PolygonCyclicAtlas.toBase K n h)
    (completeClosedFiber_isPullback K n h) V k hV he

variable {T : Scheme} (g : T ⟶ Spec (.of K))
  (a : UniversalWeierstrass.Labels 4 →* (Over.mk g ⟶ G K n))
  (b : UniversalWeierstrass.Labels 3 →* (Over.mk g ⟶ G K n))
local notation "f" => completeBoundaryTestParameter K n h g a b

/-- The actual cyclic homomorphism is precisely the original marking's base change. -/
theorem completeBoundaryTestParameter_hom :
    cyclicSectionMarking (G K n) n g (f) =
      pullCyclicMarking (E := EC) g (completeClosedBoundaryMarking K n h) := by
  apply MonoidHom.ext
  intro j
  rw [cyclicSectionMarking_apply, completeBoundaryTestParameter_section]
  rfl

/-- Faithfulness of the complete cyclic subgroup is preserved on every original boundary test. -/
theorem completeBoundaryTestParameter_distinct :
    UniversallyDistinctSections.UniversallyDistinct
      (fun i : ZMod n ↦ cyclicSectionMarking (G K n) n g (f) (.ofAdd i)) := by
  rw [completeBoundaryTestParameter_hom]
  exact pullCyclicMarking_distinct (E := EC) g (completeClosedBoundaryMarking K n h)
    (completeClosedBoundaryMarking_distinct K n h)

end FLT.Mazur.PolygonInfinitesimalStages
