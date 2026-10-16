/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RelativeRelationInvariantPrincipal

/-!
# Original denominators nonvanishing at an orbit point

Principal neighborhoods of a fixed point define a multiplicative set in the
original invariant section ring. Products remain nonvanishing at that point,
without a scheme structure or affineness assumption on the quotient.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
universe u
namespace FLT.Mazur.RelativeRelationOrbit
variable {S : Scheme.{u}} {A U : Over S} {p q : A ⟶ U}
  (e : CategoryTheory.EquivalenceRelation p q) (W : Opens (Orbit e))
  (x : Orbit e) (hx : x ∈ W)

/-- Original invariant sections whose actual principal neighborhoods contain the given point. -/
def pointDenominators : Submonoid ((invariantSheaf e).obj.obj (op W)) where
  carrier := {a | x ∈ invariantPrincipal e W a}
  one_mem' := by
    change x ∈ invariantPrincipal e W 1
    simpa only [invariantPrincipal_one] using hx
  mul_mem' {a b} ha hb := by
    change x ∈ invariantPrincipal e W (a * b)
    rw [invariantPrincipal_mul]
    exact ⟨ha, hb⟩

/-- Membership is actual nonvanishing in the original quotient, not in a coefficient model. -/
theorem mem_pointDenominators (a : (invariantSheaf e).obj.obj (op W)) :
    a ∈ pointDenominators e W x hx ↔ x ∈ invariantPrincipal e W a := Iff.rfl

/-- The multiplicative set is precisely the original sections with invertible germs. -/
theorem mem_pointDenominators_iff_isUnit (a : (invariantSheaf e).obj.obj (op W)) :
    a ∈ pointDenominators e W x hx ↔
      IsUnit (TopCat.Presheaf.germ (invariantSheaf e).obj W x hx a) :=
  (invariantLocallyRingedSpace e).toRingedSpace.mem_basicOpen a x hx

/-- Every chosen denominator gives an actual original neighborhood of the specified point. -/
theorem pointDenominator_mem (a : pointDenominators e W x hx) :
    x ∈ invariantPrincipal e W a.val := a.property

/-- With affine source, every allowed denominator has an affine source principal neighborhood. -/
theorem pointDenominator_source_affine (hW : IsAffineOpen (pullOpen e W).val)
    (a : pointDenominators e W x hx) :
    IsAffineOpen (pullOpen e (invariantPrincipal e W a.val)).val :=
  invariantPrincipal_source_affine e W hW a.val

end FLT.Mazur.RelativeRelationOrbit
