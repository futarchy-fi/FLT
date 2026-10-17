/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteSmoothOriginalSubgroupIso

/-!
# The smooth field comparison preserves the original Cartier generator

The subgroup comparison sends the pulled-back original generator to the original
field generator as an actual section. Every power is preserved as well.
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
variable (L : Type) [Field L] (a : PowerSeries K →+* L) (ha : a PowerSeries.X ≠ 0)
  {Y : Scheme} (p : Y ⟶ exactVeroneseProj K n h) (q : Y ⟶ Spec (.of L))
  (hs : IsPullback p q (exactVeroneseProjToBase K n h)
    (Spec.map (CommRingCat.ofHom a)))
local notation "b" => Spec.map (CommRingCat.ofHom a)
local notation "H" => completeOriginalFiniteSubgroup K n h
local notation "J" => completeFieldFiniteSubgroup K n h L a ha p q hs
local notation "P" => completeOriginalGenerator K n h
local notation "Q" => completeFieldGenerator K n h L a ha p q hs
local notation "e" => completeSmoothOriginalCurveIso K n h L a ha p q hs
local notation "c" => completeSmoothOriginalSubgroupIso K n h L a ha p q hs

/-- The original field label one is the actual pullback of the complete generator point. -/
theorem completeSmoothOriginalGenerator_curve_comparison :
    (Q) ≫ (J).curveMap ≫ (e).hom.curve =
      GroupSectionBaseChange.pullSection b ((P) ≫ (H).curveMap) := by
  have hP := completeOriginalGenerator_orbit K n h (⟨1, h⟩ : Fin n)
  have hQ := completeFieldGenerator_orbit K n h L a ha p q hs (⟨1, h⟩ : Fin n)
  simp only [pow_one] at hP hQ
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · simp only [Over.comp_left, Category.assoc, completeSmoothOriginalCurveIso_fst]
    rw [← Category.assoc, ← Over.comp_left, hQ, completeCartesianMarking_fst,
      GroupSectionBaseChange.section_fst, hP]
  · exact ((Q) ≫ (J).curveMap ≫ (e).hom.curve).w.trans
      (GroupSectionBaseChange.pullSection b ((P) ≫ (H).curveMap)).w.symm

/-- The full compatible comparison retains the actual original Cartier generator. -/
theorem completeSmoothOriginalSubgroupIso_generator :
    GroupSectionBaseChange.pullSection b (P) ≫ (c).subgroup.hom = Q := by
  have : Mono (J).curveMap := Over.mono_of_mono_left _
  have : IsIso (e).hom.curve := inferInstanceAs (IsIso (forgetCurve.map (e).hom))
  apply (cancel_mono (J).curveMap).mp
  rw [Category.assoc, ← (c).compatible, ← Category.assoc, baseChange_curveMap,
    ← GroupSectionBaseChange.section_comp, completeSmoothOriginalSubgroupIso_curve]
  apply (cancel_mono (e).hom.curve).mp
  have he := congrArg GeneralizedEllipticCurve.Hom.curve (e).inv_hom_id
  change (e).inv.curve ≫ (e).hom.curve = 𝟙 _ at he
  change (_ ≫ (e).inv.curve) ≫ (e).hom.curve = _
  rw [Category.assoc, he, Category.comp_id]
  exact (completeSmoothOriginalGenerator_curve_comparison K n h L a ha p q hs).symm

/-- Every power remains the same original field subgroup section. -/
theorem completeSmoothOriginalSubgroupIso_generator_pow (m : ℕ) :
    GroupSectionBaseChange.pullSection b ((P) ^ m) ≫ (c).subgroup.hom = (Q) ^ m := by
  rw [GroupSectionBaseChange.section_pow, MonObj.pow_comp,
    completeSmoothOriginalSubgroupIso_generator]

end FLT.Mazur.PolygonInfinitesimalStages
