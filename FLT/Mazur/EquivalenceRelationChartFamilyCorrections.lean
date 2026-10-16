/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EquivalenceRelationMixedChartDescent
public import FLT.Mazur.EquivalenceRelationBoundaryOpenCoefficients
public import FLT.Mazur.InvariantSectionObstruction

/-!
# Simultaneous corrections across an entire family of independent frame charts

The correction group uses one invariant section per chart, shared by every
mixed relation meeting that chart. Its obstruction vanishes exactly when a
single family of kernel corrections makes all mixed equations hold together.
Separate solutions for individual pairs are not sufficient for this criterion.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationNormalizedFrames.MixedFrames.ChartFamily
open SchemeFiniteGroupQuotient FiniteGroupRestriction InvariantSectionObstruction
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] EquivalenceRelationNormalizedFrames.source
  InvariantBoundary.boundary MixedFrames.relation jointBoundaryTarget
variable {D A B : Scheme.{0}} {p q : D ⟶ A} [IsSeparated p]
  (e : CategoryTheory.EquivalenceRelation p q)
  {ι : Type} (n : ι → ℕ) (o : ∀ a, Fin (n a))
  (U : ∀ a, (source p q (Fin (n a)) (o a)).Opens)
  (hU : ∀ a σ, (action e (Fin (n a)) (o a) σ).hom ⁻¹ᵁ U a = U a)

/-- A simultaneous family of finite-action invariant ambient sections. -/
abbrev Sections := ∀ a, invariantCoordinates
  (restrictedAction (action e (Fin (n a)) (o a)) (U a) (hU a))

/-- All differences on the entire original mixed relations, with one shared lift per chart. -/
def difference : Sections e n o U hU →+
    ∀ a b, Γ((mixedChartOpen (o a) (o b) (U a) (U b)).toScheme, ⊤) where
  toFun s a b := (mixedChartFirst (o a) (o b) (U a) (U b)).appTop (s a).val -
    (mixedChartSecond (o a) (o b) (U a) (U b)).appTop (s b).val
  map_zero' := by
    funext a b
    change (mixedChartFirst (o a) (o b) (U a) (U b)).appTop 0 -
      (mixedChartSecond (o a) (o b) (U a) (U b)).appTop 0 = 0
    simp only [map_zero, sub_self]
  map_add' s t := by
    funext a b
    change (mixedChartFirst (o a) (o b) (U a) (U b)).appTop ((s a).val + (t a).val) -
      (mixedChartSecond (o a) (o b) (U a) (U b)).appTop ((s b).val + (t b).val) = _
    simp only [map_add, Pi.add_apply]
    abel

/-- The difference is computed on the unchanged mixed relation, not a selected common frame. -/
theorem difference_apply (s : Sections e n o U hU) (a b : ι) :
    difference e n o U hU s a b =
      (mixedChartFirst (o a) (o b) (U a) (U b)).appTop (s a).val -
        (mixedChartSecond (o a) (o b) (U a) (U b)).appTop (s b).val := rfl

variable (i : B ⟶ A)

/-- Actual restriction of every invariant chart section to its whole closed boundary. -/
def restriction : Sections e n o U hU →+
    ∀ a, Γ((InvariantBoundary.inclusion (Fin (n a)) (o a) i ⁻¹ᵁ U a).toScheme, ⊤) where
  toFun s a := (InvariantBoundary.inclusion (Fin (n a)) (o a) i ∣_ U a).appTop (s a).val
  map_zero' := by
    funext a
    exact map_zero _
  map_add' s t := by
    funext a
    exact map_add _ _ _

/-- The canonical family discrepancy modulo simultaneous invariant boundary-kernel corrections. -/
def defect : Sections e n o U hU →+
    (∀ a b, Γ((mixedChartOpen (o a) (o b) (U a) (U b)).toScheme, ⊤)) ⧸
      corrections (restriction e n o U hU i) (difference e n o U hU) :=
  InvariantSectionObstruction.defect
    (restriction e n o U hU i) (difference e n o U hU)

/-- Changing all lifts while retaining their exact boundary values leaves the obstruction fixed. -/
theorem defect_eq_of_restriction_eq {s t : Sections e n o U hU}
    (h : restriction e n o U hU i s = restriction e n o U hU i t) :
    defect e n o U hU i s = defect e n o U hU i t :=
  InvariantSectionObstruction.defect_eq_of_restrict_eq _ _ h

/-- Vanishing gives a single family of actual corrections in the original boundary kernels. -/
theorem defect_eq_zero_iff_correction (s : Sections e n o U hU) :
    defect e n o U hU i s = 0 ↔ ∃ t : Sections e n o U hU,
      restriction e n o U hU i t = 0 ∧
        difference e n o U hU t = difference e n o U hU s :=
  InvariantSectionObstruction.defect_eq_zero_iff _ _ s

/-- The obstruction vanishes exactly when one corrected family satisfies every mixed equation. -/
theorem defect_eq_zero_iff_compatible (s : Sections e n o U hU) :
    defect e n o U hU i s = 0 ↔ ∃ t : Sections e n o U hU,
      restriction e n o U hU i t = restriction e n o U hU i s ∧
        ∀ a b, (mixedChartFirst (o a) (o b) (U a) (U b)).appTop (t a).val =
          (mixedChartSecond (o a) (o b) (U a) (U b)).appTop (t b).val := by
  rw [defect, InvariantSectionObstruction.defect_eq_zero_iff_invariant_lift]
  constructor
  · rintro ⟨t, ht, hd⟩
    refine ⟨t, ht, fun a b ↦ sub_eq_zero.mp ?_⟩
    exact congrFun (congrFun hd a) b
  · rintro ⟨t, ht, hd⟩
    refine ⟨t, ht, ?_⟩
    funext a b
    exact sub_eq_zero.mpr (hd a b)

variable [Etale p]

/-- The same simultaneous correction criterion can be tested on every bounded common frame. -/
theorem defect_eq_zero_iff_common_frames (s : Sections e n o U hU) :
    defect e n o U hU i s = 0 ↔ ∃ t : Sections e n o U hU,
      restriction e n o U hU i t = restriction e n o U hU i s ∧
        ∀ a b (c : JointIndex (Fin (n a)) (Fin (n b))),
          (jointChartFirst e (o a) (o b) c.2.val.1 c.2.val.2 (U a) (U b)).appTop
            (t a).val =
          (jointChartSecond e (o a) (o b) c.2.val.1 c.2.val.2 (U a) (U b)).appTop
            (t b).val := by
  rw [defect_eq_zero_iff_compatible]
  constructor
  · rintro ⟨t, ht, hd⟩
    exact ⟨t, ht, fun a b ↦
      (mixedChart_compatible_iff e (o a) (o b) (U a) (U b) _ _).mp (hd a b)⟩
  · rintro ⟨t, ht, hd⟩
    exact ⟨t, ht, fun a b ↦
      (mixedChart_compatible_iff e (o a) (o b) (U a) (U b) _ _).mpr (hd a b)⟩

end FLT.Mazur.EquivalenceRelationNormalizedFrames.MixedFrames.ChartFamily
