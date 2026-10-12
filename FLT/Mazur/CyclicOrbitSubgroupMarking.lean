/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicDivisorSubgroupCriterion

/-!
# Lifting all cyclic labels to the actual orbit subgroup

If a finite subgroup has the full cyclic orbit ideal, each marked section
factors through its actual closed carrier. Cancellation of the inclusion
proves that these lifts form a cyclic homomorphism.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory MonObj
namespace FLT.Mazur.GeneralizedEllipticCurve.FiniteSubgroup
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {S : Scheme} {E : GeneralizedEllipticCurve S} {n : ℕ} [NeZero n]
  (H : E.FiniteSubgroup n)
  (φ : Multiplicative (ZMod n) →* (𝟙_ (Over S) ⟶ E.group))
  (hI : H.ideal = E.cyclicMarkingIdeal φ)

/-- Every cyclic label factors through the original closed subgroup carrier. -/
def orbitSection (i : Multiplicative (ZMod n)) : 𝟙_ (Over S) ⟶ H.carrier :=
  Over.homMk (IsClosedImmersion.lift H.curveMap.left (φ i ≫ E.inclusion).left (by
    change H.ideal ≤ _
    rw [hI]
    exact E.cyclicMarkingIdeal_le_section φ i.toAdd)) (by
      rw [← H.curveMap.w, ← Category.assoc, IsClosedImmersion.lift_fac]
      exact Over.w _)

/-- Lifting a label retains its original whole-curve section. -/
@[reassoc] theorem orbitSection_curveMap (i : Multiplicative (ZMod n)) :
    H.orbitSection φ hI i ≫ H.curveMap = φ i ≫ E.inclusion := by
  apply Over.OverMorphism.ext
  exact IsClosedImmersion.lift_fac _ _ _

/-- Lifting a label retains its original smooth-group section. -/
@[reassoc] theorem orbitSection_inclusion (i : Multiplicative (ZMod n)) :
    H.orbitSection φ hI i ≫ H.inclusion = φ i := by
  have : Mono E.inclusion := Over.mono_of_mono_left E.inclusion
  apply (cancel_mono E.inclusion).mp
  exact (Category.assoc _ _ _).trans (H.orbitSection_curveMap φ hI i)

/-- The lifted labels form a homomorphism in the actual subgroup scheme. -/
def orbitMarking : Multiplicative (ZMod n) →* (𝟙_ (Over S) ⟶ H.carrier) where
  toFun := H.orbitSection φ hI
  map_one' := by
    have : Mono H.inclusion := Over.mono_of_mono_left H.inclusion
    apply (cancel_mono H.inclusion).mp
    rw [orbitSection_inclusion, map_one, one_comp]
  map_mul' i j := by
    have : Mono H.inclusion := Over.mono_of_mono_left H.inclusion
    apply (cancel_mono H.inclusion).mp
    rw [orbitSection_inclusion, mul_comp, orbitSection_inclusion,
      orbitSection_inclusion, map_mul]

/-- The lifted cyclic homomorphism realizes precisely the prescribed original marking. -/
@[reassoc] theorem orbitMarking_inclusion (i : Multiplicative (ZMod n)) :
    H.orbitMarking φ hI i ≫ H.inclusion = φ i := H.orbitSection_inclusion φ hI i

end FLT.Mazur.GeneralizedEllipticCurve.FiniteSubgroup
