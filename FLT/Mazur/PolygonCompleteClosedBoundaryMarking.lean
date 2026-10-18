/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteClosedCartierGenerator
public import FLT.Mazur.CyclicBoundaryOriginalMarkings

/-!
# Original complete closed subgroup markings as boundary parameters

The cyclic marking passes through the actual complete closed divisor. Together
with two independent auxiliary markings it defines a test of the boundary
parameter scheme. Every cyclic label recovers its original full-group section.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory MonObj
namespace FLT.Mazur.PolygonInfinitesimalStages
open PolygonPinching PolygonUniversalAction CyclicBoundaryParameter
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]
local notation "S" => Spec (CommRingCat.of K)
local notation "H" => completeClosedFiniteSubgroup K n h
local notation "e" => completeCyclicDivisorIso K n h (completeClosedBase K)
  (completeClosedFiberInclusion K n h) (PolygonCyclicAtlas.toBase K n h)
  (completeClosedFiber_isPullback K n h)

/-- All original complete closed divisor labels, mapped into the unchanged full polygon group. -/
def completeClosedBoundaryMarking : Multiplicative (ZMod n) →*
    (𝟙_ (Over S) ⟶ G K n) where
  toFun a := ConstantCyclicGroup.component (S) n a.toAdd ≫ (e).hom ≫ (H).inclusion
  map_one' := by
    change _ ≫ (e).hom ≫ (e).inv ≫ _ = _
    rw [Iso.hom_inv_id_assoc, toAdd_one, ConstantCyclicGenerator.component_zero, MonObj.one_comp]
  map_mul' a b := by
    change (_ ≫ (e).hom ≫ (e).inv ≫ _) =
      (_ ≫ (e).hom ≫ (e).inv ≫ _) * (_ ≫ (e).hom ≫ (e).inv ≫ _)
    simp only [Iso.hom_inv_id_assoc, toAdd_mul,
      ConstantCyclicGenerator.component_add, MonObj.mul_comp]

/-- The marking uses precisely the original all-one subgroup in the full smooth group. -/
theorem completeClosedBoundaryMarking_eq (a : Multiplicative (ZMod n)) :
    completeClosedBoundaryMarking K n h a =
      ConstantCyclicGroup.component (S) n a.toAdd ≫ ConstantCyclicInclusion.inclusion K n := by
  change _ ≫ (e).hom ≫ (e).inv ≫ _ = _
  rw [Iso.hom_inv_id_assoc]

/-- The specified cyclic generator remains the generator of the original complete divisor. -/
theorem completeClosedBoundaryMarking_generator :
    completeClosedBoundaryMarking K n h (.ofAdd 1) =
      completeClosedGenerator K n h ≫ (H).inclusion := by
  exact (Category.assoc (ConstantCyclicGroup.component (S) n 1)
    (e).hom (H).inclusion).symm

variable (a : UniversalWeierstrass.Labels 4 →* (𝟙_ (Over (Spec (.of K))) ⟶ G K n))
  (b : UniversalWeierstrass.Labels 3 →* (𝟙_ (Over (Spec (.of K))) ⟶ G K n))

/-- The actual parameter test supplied by the original complete subgroup and auxiliary markings. -/
def completeClosedBoundaryParameter : 𝟙_ (Over S) ⟶ CyclicBoundaryParameter.parameter (G K n) n :=
  ofMarkings (G K n) n a b (completeClosedBoundaryMarking K n h)

/-- The parameter retains every label of the actual original complete subgroup. -/
@[reassoc] theorem completeClosedBoundaryParameter_cyclic (j : Multiplicative (ZMod n)) :
    completeClosedBoundaryParameter K n h a b ≫ AuxiliaryLevel.value (G K n) (Label n)
      (1, 1, j) = completeClosedBoundaryMarking K n h j :=
  ofMarkings_cyclic (G K n) n a b (completeClosedBoundaryMarking K n h) j

/-- Every original auxiliary level-four label is retained independently of the subgroup. -/
@[reassoc] theorem completeClosedBoundaryParameter_four (j : UniversalWeierstrass.Labels 4) :
    completeClosedBoundaryParameter K n h a b ≫ AuxiliaryLevel.value (G K n) (Label n)
      (j, 1, 1) = a j :=
  ofMarkings_four (G K n) n a b (completeClosedBoundaryMarking K n h) j

/-- Every original auxiliary level-three label is retained independently of the subgroup. -/
@[reassoc] theorem completeClosedBoundaryParameter_three (j : UniversalWeierstrass.Labels 3) :
    completeClosedBoundaryParameter K n h a b ≫ AuxiliaryLevel.value (G K n) (Label n)
      (1, j, 1) = b j :=
  ofMarkings_three (G K n) n a b (completeClosedBoundaryMarking K n h) j

end FLT.Mazur.PolygonInfinitesimalStages
