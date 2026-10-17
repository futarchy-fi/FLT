/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteClosedSubgroupIso

/-!
# The closed comparison preserves the original Cartier generator

The subgroup comparison sends the pulled-back original generator to the original
closed generator as an actual section. Every power is preserved as well.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory MonObj
open scoped CategoryTheory.Obj
namespace FLT.Mazur.PolygonInfinitesimalStages
open GeneralizedEllipticCurve GeneralizedEllipticCurve.FiniteSubgroup
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]
local notation "b" => completeClosedBase K
local notation "H" => completeOriginalFiniteSubgroup K n h
local notation "J" => completeClosedFiniteSubgroup K n h
local notation "P" => completeOriginalGenerator K n h
local notation "Q" => completeClosedGenerator K n h
local notation "e" => completeClosedCurveIso K n h
local notation "c" => completeClosedSubgroupIso K n h

/-- The original closed label one is the actual pullback of the complete generator point. -/
theorem completeClosedGenerator_curve_comparison :
    (Q) ≫ (J).curveMap ≫ (e).hom.curve =
      GroupSectionBaseChange.pullSection b ((P) ≫ (H).curveMap) := by
  have hP := completeOriginalGenerator_orbit K n h (⟨1, h⟩ : Fin n)
  have hQ := completeClosedGenerator_orbit K n h (⟨1, h⟩ : Fin n)
  simp only [pow_one] at hP hQ
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · simp only [Over.comp_left, Category.assoc, completeClosedCurveIso_fst]
    rw [← Category.assoc, ← Over.comp_left, hQ, completeCartesianMarking_fst,
      GroupSectionBaseChange.section_fst, hP]
  · exact ((Q) ≫ (J).curveMap ≫ (e).hom.curve).w.trans
      (GroupSectionBaseChange.pullSection b ((P) ≫ (H).curveMap)).w.symm

/-- The full compatible comparison retains the actual original Cartier generator. -/
theorem completeClosedSubgroupIso_generator :
    GroupSectionBaseChange.pullSection b (P) ≫ (c).subgroup.hom = Q := by
  have : Mono (J).curveMap := Over.mono_of_mono_left _
  have : IsIso (e).hom.curve := inferInstanceAs (IsIso (forgetCurve.map (e).hom))
  apply (cancel_mono (J).curveMap).mp
  rw [Category.assoc, ← (c).compatible, ← Category.assoc, baseChange_curveMap,
    ← GroupSectionBaseChange.section_comp, completeClosedSubgroupIso_curve]
  apply (cancel_mono (e).hom.curve).mp
  have he := congrArg GeneralizedEllipticCurve.Hom.curve (e).inv_hom_id
  change (e).inv.curve ≫ (e).hom.curve = 𝟙 _ at he
  change (_ ≫ (e).inv.curve) ≫ (e).hom.curve = _
  rw [Category.assoc, he, Category.comp_id]
  exact (completeClosedGenerator_curve_comparison K n h).symm

/-- Every power remains the same original closed subgroup section. -/
theorem completeClosedSubgroupIso_generator_pow (m : ℕ) :
    GroupSectionBaseChange.pullSection b ((P) ^ m) ≫ (c).subgroup.hom = (Q) ^ m := by
  rw [GroupSectionBaseChange.section_pow, MonObj.pow_comp,
    completeClosedSubgroupIso_generator]

end FLT.Mazur.PolygonInfinitesimalStages
