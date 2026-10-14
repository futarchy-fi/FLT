/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteSmoothFieldCoefficientSubgroup
public import FLT.Mazur.PolygonCompleteSmoothFieldCoefficientMarking

/-!
# The original Cartier generator survives coefficient extension

The actual compatible subgroup comparison preserves the chosen generator, not
only its orbit ideal. Consequently it preserves every power as a subgroup section.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory MonObj
open scoped CategoryTheory.Obj
namespace FLT.Mazur.PolygonInfinitesimalStages
open GeneralizedEllipticCurve GeneralizedEllipticCurve.FiniteSubgroup
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]
  (L : Type) [Field L] (a : PowerSeries K →+* L) (ha : a PowerSeries.X ≠ 0)
  {Y : Scheme} (p : Y ⟶ exactVeroneseProj K n h) (q : Y ⟶ Spec (.of L))
  (hs : IsPullback p q (exactVeroneseProjToBase K n h)
    (Spec.map (CommRingCat.ofHom a)))
  (M : Type) [Field M] [Algebra L M]
  {Z : Scheme} (r : Z ⟶ exactVeroneseProj K n h) (s : Z ⟶ Spec (.of M))
  (ht : IsPullback r s (exactVeroneseProjToBase K n h)
    (Spec.map (CommRingCat.ofHom ((algebraMap L M).comp a))))
local notation "aM" => RingHom.comp (algebraMap L M) a
local notation "haM" => Iff.mpr (map_ne_zero (algebraMap L M)) ha
local notation "b" => Spec.map (CommRingCat.ofHom (algebraMap L M))
local notation "H" => completeFieldFiniteSubgroup K n h L a ha p q hs
local notation "J" => completeFieldFiniteSubgroup K n h M aM haM r s ht
local notation "e" => completeFieldCoefficientCurveIso K n h L a ha p q hs M r s ht (0 : Fin n)

local notation "c" => completeFieldCoefficientSubgroupIso K n h L a ha p q hs M r s ht
local notation "P" => completeFieldGenerator K n h L a ha p q hs
local notation "Q" => completeFieldGenerator K n h M aM haM r s ht

/-- The original generator maps to the original label one in the full field curve. -/
theorem completeFieldGenerator_curvePoint :
    P ≫ (H).curveMap = completeFieldMarkedPoint K n h L a p q hs ⟨1, h⟩ := by
  apply Over.OverMorphism.ext
  change (P ≫ (H).curveMap).left =
    completeCartesianMarking K n h (Spec.map (CommRingCat.ofHom a)) p q hs ⟨1, h⟩
  simpa only [pow_one] using
    completeFieldGenerator_orbit K n h L a ha p q hs (⟨1, h⟩ : Fin n)

/-- The full coefficient comparison preserves the actual chosen Cartier generator. -/
theorem completeFieldCoefficientSubgroupIso_generator :
    GroupSectionBaseChange.pullSection b P ≫ (c).subgroup.hom = Q := by
  have hm : Mono (J).curveMap := by
    apply (Over.forget _).mono_of_mono_map
    change Mono (J).curveMap.left
    rw [completeFieldFiniteSubgroup_curveMap]
    infer_instance
  apply (cancel_mono (J).curveMap).mp
  rw [Category.assoc, ← (c).compatible, ← Category.assoc,
    baseChange_curveMap, ← GroupSectionBaseChange.section_comp,
    completeFieldGenerator_curvePoint, completeFieldCoefficientSubgroupIso_curve,
    completeFieldCoefficientCurveIso_marking_hom, completeFieldGenerator_curvePoint]

/-- Every power of the chosen original generator is preserved as an actual subgroup section. -/
theorem completeFieldCoefficientSubgroupIso_generator_pow (m : ℕ) :
    GroupSectionBaseChange.pullSection b (P ^ m) ≫ (c).subgroup.hom = Q ^ m := by
  erw [GroupSectionBaseChange.section_pow, MonObj.pow_comp,
    completeFieldCoefficientSubgroupIso_generator]

end FLT.Mazur.PolygonInfinitesimalStages
