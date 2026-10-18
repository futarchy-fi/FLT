/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteClosedBoundaryMarking

/-!
# The actual complete subgroup divisor on its boundary parameter test

The cyclic labels of the boundary test are precisely the original complete
Cartesian markings. Their full product ideal is the original complete closed
subgroup ideal, so the parameter retains its proved ampleness.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory MonObj
namespace FLT.Mazur.PolygonInfinitesimalStages
open PolygonPinching PolygonUniversalAction CyclicBoundaryParameter FCurve
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
attribute [local instance] completeClosedPolygon_lfp cyclic_lfp
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]
local notation "S" => Spec (CommRingCat.of K)
local notation "H" => completeClosedFiniteSubgroup K n h
local notation "p" => PolygonCyclicAtlas.normalization K n h
local notation "q" => PolygonCyclicAtlas.nodes K n h
local notation "hn" => (Nat.lt_of_lt_of_le (Nat.succ_pos 1) h)
local notation "hp" => PolygonCyclicPushout.isPushout K n h hn
local notation "b₀" => completeClosedBase K
local notation "j₀" => completeClosedFiberInclusion K n h
local notation "q₀" => PolygonCyclicAtlas.toBase K n h
local notation "hb" => completeClosedFiber_isPullback K n h

/-- Every actual boundary label is the indicated power of the original complete generator. -/
theorem completeClosedBoundaryMarking_pow (r : ℕ) :
    completeClosedBoundaryMarking K n h (.ofAdd (r : ZMod n)) =
      completeClosedBoundaryMarking K n h (.ofAdd 1) ^ r := by
  rw [← map_pow]
  congr 1
  simp only [← ofAdd_nsmul, nsmul_eq_mul, _root_.mul_one]

variable (a : UniversalWeierstrass.Labels 4 →* (𝟙_ (Over (Spec (.of K))) ⟶ G K n))
  (b : UniversalWeierstrass.Labels 3 →* (𝟙_ (Over (Spec (.of K))) ⟶ G K n))
local notation "f" => completeClosedBoundaryParameter K n h a b
local notation "u" => PolygonActionSmooth.smoothMap K n hn (p) (q) (hp)

/-- Every original complete Cartesian marking is the actual cyclic boundary-parameter label. -/
theorem completeClosedBoundaryParameter_curve (i : Fin n) :
    (((f) ≫ AuxiliaryLevel.value (G K n) (Label n)
      (1, 1, .ofAdd (i.val : ZMod n))) ≫ (u)).left =
        completeCartesianMarking K n h (b₀) (j₀) (q₀) (hb) i := by
  rw [completeClosedBoundaryParameter_cyclic, completeClosedBoundaryMarking_pow,
    completeClosedBoundaryMarking_generator, ← MonObj.pow_comp, Category.assoc]
  exact completeClosedGenerator_orbit K n h i

/-- The full product of actual parameter labels retains the original complete subgroup ideal. -/
theorem completeClosedBoundaryParameter_ideal :
    (∏ i : Fin n, (((f) ≫ AuxiliaryLevel.value (G K n) (Label n)
      (1, 1, .ofAdd (i.val : ZMod n))) ≫ (u)).left.ker) = (H).ideal := by
  simp only [completeClosedBoundaryParameter_curve, completeClosedFiniteSubgroup_ideal,
    completeMarkingDivisor, idealSheaf_comap_prod,
    completeCartesianMarking_ker K n h (b₀) (j₀) (q₀) (hb)]

/-- The actual parameter divisor retains the original closed subgroup's Cartier property. -/
theorem completeClosedBoundaryParameter_cartier :
    RelativeEffectiveCartier (PolygonCyclicAtlas.polygon K n h).hom
      (∏ i : Fin n, (((f) ≫ AuxiliaryLevel.value (G K n) (Label n)
        (1, 1, .ofAdd (i.val : ZMod n))) ≫ (u)).left.ker) := by
  rw [completeClosedBoundaryParameter_ideal]
  exact completeClosedFiniteSubgroup_relativeCartier K n h

/-- The actual boundary parameter's full original divisor line is relatively ample. -/
theorem completeClosedBoundaryParameter_ample :
    RelativeAmple (PolygonCyclicAtlas.polygon K n h).hom
      (divisorLineBundle
        (∏ i : Fin n, (((f) ≫ AuxiliaryLevel.value (G K n) (Label n)
          (1, 1, .ofAdd (i.val : ZMod n))) ≫ (u)).left.ker)
        (completeClosedBoundaryParameter_cartier K n h a b).1) := by
  obtain ⟨hI, hA⟩ := completeClosedFiniteSubgroup_isAmple K n h
  change RelativeAmple (PolygonCyclicAtlas.polygon K n h).hom _ at hA
  simpa only [divisorLineBundle, completeClosedBoundaryParameter_ideal] using hA

end FLT.Mazur.PolygonInfinitesimalStages
