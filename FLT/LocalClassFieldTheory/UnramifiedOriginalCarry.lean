/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.UnramifiedStageCarryInflation
public import FLT.LocalClassFieldTheory.UnramifiedInflatedCarries

/-!
# The finite carry in the separable closure

Transport the Frobenius coordinates through the actual inclusion of the finite
stage into the unramified union. Direct and successive inflation agree.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace LocalClassFieldTheory

open IsLocalRing CategoryTheory HomologicalComplex groupCohomology

variable (R K C : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Field K] [Algebra R K] [IsFractionRing R K]
  [Field C] [Algebra K C] [Algebra R C] [IsScalarTower R K C]
  [Algebra.IsSeparable K C] [Finite (ResidueField R)] [IsSepClosed C]
  [IsAdicComplete (maximalIdeal R) R]
  {π : R} (hπ : Irreducible π) (n : UnramifiedIndex)

local notation "U" => maximalUnramified R K C
local notation "E" => unramifiedStage R K C n.degree
local notation "F" => unramifiedFiniteStage R K C n

/-- The original stage is finite over the base. -/
local instance unramifiedOriginalCarryFinite : FiniteDimensional K E :=
  (unramifiedStage_isUnramified R K C n.degree).1
/-- The original stage is Galois over the base. -/
local instance unramifiedOriginalCarryGalois : IsGalois K E := by
  let := (unramifiedStage_isUnramified R K C n.degree).normal
  exact ⟨⟩
/-- Discrete finite-stage coefficients in the original field presentation. -/
local instance unramifiedOriginalCarryTopology : TopologicalSpace (Additive Eˣ) := ⊥
local instance unramifiedOriginalCarryDiscrete : DiscreteTopology (Additive Eˣ) := ⟨rfl⟩

attribute [local instance] unramifiedUnionGalois fieldUnitAction
  unramifiedFieldUnitTopology unramifiedFieldUnitDiscrete
  separableClosureGalois separableClosureUnitTopology separableClosureUnitDiscrete
  trivialCoefficientAction trivialCoefficientIntComm trivialCoefficientContinuous

/-- The canonical field equivalence between the two presentations of the stage. -/
def unramifiedCarryFieldEquiv : E ≃ₐ[K] F :=
  IntermediateField.restrictAlgEquiv (unramifiedStage_le_maximalUnramified R K C n.degree)

/-- The original stage's cyclic coordinate, transported from actual arithmetic Frobenius. -/
def unramifiedOriginalCarryCoordinate : Gal(E/K) ≃* Multiplicative (ZMod n.degree) :=
  (AlgEquiv.autCongr (unramifiedCarryFieldEquiv R K C n)).trans
    (unramifiedStageCyclicEquiv R K C n).symm

/-- Restriction from the closure agrees in both presentations of the finite stage. -/
theorem unramifiedCarry_restriction (g : Gal(C/K)) :
    AlgEquiv.autCongr (unramifiedCarryFieldEquiv R K C n) (g.restrictNormal E) =
      (g.restrictNormal U).restrictNormal F := by
  ext y
  obtain ⟨y, rfl⟩ := (unramifiedCarryFieldEquiv R K C n).surjective y
  simp only [AlgEquiv.autCongr_apply, AlgEquiv.trans_apply, AlgEquiv.symm_apply_apply]
  exact (AlgEquiv.restrictNormal_apply E g y).trans
    ((AlgEquiv.restrictNormal_apply U g
      ((unramifiedCarryFieldEquiv R K C n) y).val).symm.trans
      (congrArg Subtype.val (AlgEquiv.restrictNormal_apply F (g.restrictNormal U)
        ((unramifiedCarryFieldEquiv R K C n) y))).symm)

local notation "M" => Rep.ofAlgebraAutOnUnits K E
local notation "e" => unramifiedOriginalCarryCoordinate R K C n
local notation "x" => finiteUnitInvariantInclusion K E (Additive.ofMul (fractionUniformizer R K hπ))

/-- Positive uniformizer carry in the original finite subfield of the closure. -/
def unramifiedOriginalOrdinaryCarry : cocycles₂ M :=
  invariantCoefficientCarry M n.degree e x

/-- The continuous class of the same original-stage carry. -/
def unramifiedOriginalContinuousCarry : continuousCohomology ℤ Gal(E/K) (Additive Eˣ) 2 :=
  (homologyMap (continuousRestriction (e).toMonoidHom continuous_of_discreteTopology
    (invariantScalarCoefficients M (e).toMonoidHom x)) 2).hom
    (integralH2Class (k := ℤ) (cyclicIntegralCarry n.degree)
      (cyclicIntegralCarry_cocycle n.degree))

/-- The continuous and ordinary carry use the same representative. -/
theorem unramifiedOriginalContinuousCarry_ordinary :
    (finiteContinuousCohomologyIso ℤ Gal(E/K) (Additive Eˣ) 2).hom
      (unramifiedOriginalContinuousCarry R K C hπ n) =
    H2π M (unramifiedOriginalOrdinaryCarry R K C hπ n) := by
  have h := finiteContinuousCohomologyIso_restriction (e).toMonoidHom
    continuous_of_discreteTopology (invariantScalarCoefficients M (e).toMonoidHom x) 2
  have he := congrArg (fun f => f.hom
    (integralH2Class (k := ℤ) (cyclicIntegralCarry n.degree)
      (cyclicIntegralCarry_cocycle n.degree))) h
  change _ = groupCohomology.map (e).toMonoidHom
    (invariantScalarCoefficients M (e).toMonoidHom x) 2
      ((finiteContinuousCohomologyIso ℤ (Multiplicative (ZMod n.degree)) ℤ 2).hom _) at he
  rw [finiteContinuousH2Class] at he
  exact he.trans (congrArg (fun f => f (cyclicOrdinaryCarry n.degree))
    (congrArg ConcreteCategory.hom (H2π_comp_map (e).toMonoidHom
      (invariantScalarCoefficients M (e).toMonoidHom x))))

end LocalClassFieldTheory
