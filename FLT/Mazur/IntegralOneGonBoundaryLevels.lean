/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ArithmeticOneGonBoundaryFiber
public import FLT.Mazur.IntegralOneGonSpecializations
public import FLT.Mazur.AmpleCyclicClassPresheaf

/-!
# Arbitrary original boundary levels on the integral degeneration's actual fiber

Every original one-gon subgroup is retained on the specified field fiber of
the cubic over Z[[t]]. Its carrier, full ideal, cyclicity and ampleness survive
the comparison. Extension off this fiber is a separate construction.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.IntegralOneGonBoundaryLevels

open OneGonSmoothing ArithmeticOneGonGeneralizedCurve IntegralOneGonSpecializations
open GeneralizedEllipticCurve.FiniteSubgroup

variable (K : Type) [Field K]
local notation "E" => PolygonGeneralizedCurve.curve K 1 Nat.zero_lt_one
  (OneGonNormalization.normalizationOver K) (OneGonNormalization.nodes K)
  (OneGonGlobalPushout.isPushout K Nat.zero_lt_one)
local notation "F" => integralPowerSeriesCurve.baseChange (boundaryMap K)

/-- The original one-gon is the full specified fiber of the actual integral degeneration. -/
def curveIso : (E) ≅ (F) := by
  let _ := (boundaryHom K).toAlgebra
  exact ArithmeticOneGonBoundaryFiber.curveIso K PowerSeries.X
    powerSeries_discriminant_factor_unit (boundaryHom_parameter K)

/-- The full comparison retains the previously constructed whole-curve boundary map. -/
theorem curveIso_curve : (curveIso K).hom.curve.left = (boundaryIso K).hom := rfl

attribute [local irreducible] curveIso

variable {n : ℕ}
  (H : (PolygonGeneralizedCurve.curve K 1 Nat.zero_lt_one
    (OneGonNormalization.normalizationOver K) (OneGonNormalization.nodes K)
    (OneGonGlobalPushout.isPushout K Nat.zero_lt_one)).FiniteSubgroup n)

/-- Any original finite subgroup on the specified actual arithmetic boundary fiber. -/
def subgroup : (F).FiniteSubgroup n := H.transport (curveIso K)

/-- The boundary comparison keeps the original subgroup carrier itself. -/
theorem subgroup_carrier : (subgroup K H).carrier = H.carrier := rfl

/-- It keeps the original inclusion, composed with the full boundary group comparison. -/
theorem subgroup_inclusion :
    (subgroup K H).inclusion = H.inclusion ≫ (curveIso K).hom.group := rfl

/-- The entire original subgroup and arithmetic-fiber subgroup are compatibly isomorphic. -/
def compatibleIso : CompatibleIso H (subgroup K H) where
  curve := curveIso K
  subgroup := Iso.refl _
  isMonHom := inferInstanceAs (IsMonHom (𝟙 H.carrier))
  compatible := by
    rw [Iso.refl_hom, Category.id_comp]
    exact (H.transport_curveMap (curveIso K)).symm

/-- The actual arithmetic boundary ideal retains all original multiplicities. -/
theorem subgroup_ideal :
    (subgroup K H).ideal = H.ideal.comap (curveIso K).inv.curve.left :=
  ideal_transport H _ (compatibleIso K H).curve (compatibleIso K H).subgroup
    (compatibleIso K H).compatible

/-- Full Cartier cyclicity is preserved, with no etaleness hypothesis on the subgroup. -/
theorem subgroup_isCyclic_iff : (subgroup K H).IsCyclic ↔ H.IsCyclic :=
  (compatibleIso K H).isCyclic_iff.symm

/-- Ampleness is preserved for the entire original subgroup divisor. -/
theorem subgroup_isAmple_iff : (subgroup K H).IsAmple ↔ H.IsAmple :=
  (compatibleIso K H).isAmple_iff.symm

/-- Any original ample cyclic subgroup gives its actual arithmetic boundary level. -/
def level (hc : H.IsCyclic) (ha : H.IsAmple) : ampleCyclicLevels (Spec (.of K)) n :=
  ⟨⟨F, subgroup K H⟩, (compatibleIso K H).isCyclic hc, (compatibleIso K H).isAmple ha⟩

/-- The full arithmetic boundary level represents precisely the original modular class. -/
theorem level_class (hc : H.IsCyclic) (ha : H.IsAmple) :
    (Quotient.mk _ (level K H hc ha) : ampleCyclicClasses (Spec (.of K)) n) =
      Quotient.mk _ ⟨⟨E, H⟩, hc, ha⟩ :=
  Quotient.sound ⟨(compatibleIso K H).symm⟩

end FLT.Mazur.IntegralOneGonBoundaryLevels
