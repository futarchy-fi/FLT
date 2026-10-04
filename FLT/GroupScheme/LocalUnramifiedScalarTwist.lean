/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.AbsoluteGaloisGroup.UnramifiedCharacterTwist
public import FLT.GroupScheme.LocalIntegralScalarUnits

/-!
# The unramified twist of the specified local model's coordinates

The coordinate action is constructed from the original coefficient action on
points by small-ramification full faithfulness. Its fixed algebra recovers the
original one over the actual character splitting ring and has finite free
coordinates. The generic point transformation is the inverse-character twist.
A descended Hopf structure on these coordinates is still required.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open NumberField IsLocalRing GaloisRepresentation.Extensions LocalRamification
open SemilinearDescent
open scoped TensorProduct
namespace ThreeAdicPlan

variable {K k : Type} [Field K] [NumberField K] [Field k]
  (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
  [IsAdicComplete (maximalIdeal (v.adicCompletionIntegers K)) (v.adicCompletionIntegers K)]
  (p : ℕ) [Fact p.Prime] [CharP k p]
  [CharP (ResidueField (v.adicCompletionIntegers K)) p]
  (X : FF (v.adicCompletionIntegers K) (v.adicCompletion K)) [Module k X.Points]
  [SMulCommClass k (AlgebraicClosure (v.adicCompletion K) ≃ₐ[v.adicCompletion K]
    AlgebraicClosure (v.adicCompletion K)) X.Points]
  (he : RaynaudParameters.order (p : v.adicCompletionIntegers K) < p - 1)
  [TopologicalSpace k] [DiscreteTopology k]
  (χ : Field.absoluteGaloisGroup (v.adicCompletion K) →* kˣ) (hc : Continuous χ)
local notation "O" => v.adicCompletionIntegers K
local notation "Kv" => v.adicCompletion K
local notation "L" => openNormalFixedField (characterOpenNormal v χ hc)
local notation "D" => IntegralClosure O L
local notation "σ" => MulSemiringAction.toAlgAut Gal(L/Kv) O D

/-- The actual integral scalar action of the character's splitting group. -/
def localUnramifiedTwistAction : Gal(L/Kv) →* (X.CoordinateRing ≃ₐ[O] X.CoordinateRing) :=
  (localIntegralUnitAction v p X he).comp (finiteModelCharacter v χ hc)

local notation "τ" => localUnramifiedTwistAction v p X he χ hc

/-- The twisting automorphism evaluates as the specified scalar on original points. -/
theorem localUnramifiedTwistAction_point (g : Gal(L/Kv)) (x : X.Points) :
    (X.integralPoints x).comp (τ g).toAlgHom =
      X.integralPoints ((finiteModelCharacter v χ hc g : k) • x) :=
  localIntegralUnitAction_point v p X he _ x

/-- The coordinate twist is finite free over the original local base. -/
theorem localUnramifiedTwist_finite_free :
    Module.Finite O (twistModel σ τ) ∧ Module.Free O (twistModel σ τ) :=
  finiteCharacter_twist_finite_free v χ hc X.CoordinateRing τ

/-- Actual scalar extension recovers the given model's original coordinates. -/
def localUnramifiedTwistEquiv (hχ : localInertiaGroup v ≤ χ.ker) :
    D ⊗[O] twistModel σ τ ≃ₐ[D] D ⊗[O] X.CoordinateRing :=
  finiteCharacterTwistEquiv v χ hc X.CoordinateRing τ hχ

/-- The constructed twist retains an etale generic coordinate algebra. -/
theorem localUnramifiedTwist_generic_etale (hχ : localInertiaGroup v ≤ χ.ker) :
    Algebra.Etale Kv (Kv ⊗[O] twistModel σ τ) :=
  finiteCharacter_twist_generic_etale v χ hc X.CoordinateRing τ hχ

/-- The splitting integral coefficients embed through their actual field in the closure. -/
local instance twistClosureAlgebra : Algebra D (AlgebraicClosure Kv) :=
  ((algebraMap L (AlgebraicClosure Kv)).comp (algebraMap D L)).toAlgebra

local instance twistClosureTower : IsScalarTower O D (AlgebraicClosure Kv) :=
  IsScalarTower.of_algebraMap_eq' rfl

variable (hχ : localInertiaGroup v ≤ χ.ker)

/-- The bijection from original points to twisted integral algebra points. -/
def localUnramifiedTwistPoints : X.Points ≃
    (twistModel σ τ →ₐ[O] AlgebraicClosure Kv) :=
  X.integralPoints.trans (finiteCharacterTwistPointsEquiv v χ hc X.CoordinateRing τ hχ _)

set_option maxHeartbeats 1000000 in
-- Comparing the integral-closure embeddings needs a larger elaboration budget.
/-- The constructed point bijection has the inverse-character Galois action. -/
theorem localUnramifiedTwistPoints_equivariant
    (γ : Field.absoluteGaloisGroup Kv) (x : X.Points) :
    (γ.toAlgHom.restrictScalars O).comp
      (localUnramifiedTwistPoints v p X he χ hc hχ x) =
    localUnramifiedTwistPoints v p X he χ hc hχ ((↑(χ γ)⁻¹ : k) • (γ • x)) := by
  let g : Gal(L/Kv) := AlgEquiv.restrictNormalHom L γ
  have hg : (γ.toAlgHom.restrictScalars O).comp (IsScalarTower.toAlgHom O D
      (AlgebraicClosure Kv)) = (IsScalarTower.toAlgHom O D (AlgebraicClosure Kv)).comp
        (σ g).toAlgHom := by
    ext s
    exact (AlgEquiv.restrictNormal_commutes γ L (algebraMap D L s)).symm
  have hchar : finiteModelCharacter v χ hc g⁻¹ = (χ γ)⁻¹ := by
    rw [map_inv, finiteModelCharacter_restrict]
  have hpoint : ((γ.toAlgHom.restrictScalars O).comp (X.integralPoints x)).comp
      (τ g⁻¹).toAlgHom = X.integralPoints ((↑(χ γ)⁻¹ : k) • (γ • x)) := by
    calc
      _ = (X.integralPoints (γ • x)).comp (τ g⁻¹).toAlgHom :=
        congrArg (fun f ↦ f.comp (τ g⁻¹).toAlgHom) (FF.integralPoints_smul X γ x).symm
      _ = X.integralPoints ((finiteModelCharacter v χ hc g⁻¹ : k) • (γ • x)) :=
        localUnramifiedTwistAction_point v p X he χ hc g⁻¹ (γ • x)
      _ = _ := congrArg (fun a : kˣ ↦ X.integralPoints ((a : k) • (γ • x))) hchar
  exact (finiteCharacterTwistPointsEquiv_equivariant v χ hc X.CoordinateRing τ hχ _
    (X.integralPoints x) (γ.toAlgHom.restrictScalars O) g hg).trans
      (congrArg (finiteCharacterTwistPointsEquiv v χ hc X.CoordinateRing τ hχ _) hpoint)

end ThreeAdicPlan
