/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.LocalUnramifiedHopfTwist

/-!
# The original group of points of the actual unramified twist

The existing fixed algebra now carries its descended Hopf structure and is
packaged as a finite-flat model. Its coefficient action is the one constructed
from the original scalar action, with no supplied descent or Hopf-law fields.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
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

local notation "τ" => localUnramifiedTwistAction v p X he χ hc

variable (hχ : localInertiaGroup v ≤ χ.ker)

/-- The splitting integers act on the closure used for the original group of points. -/
local instance twistGroupClosureAlgebra : Algebra D (AlgebraicClosure Kv) :=
  ((algebraMap L (AlgebraicClosure Kv)).comp (algebraMap D L)).toAlgebra

/-- The group-point coefficient embedding extends the original integral embedding. -/
local instance twistGroupClosureTower : IsScalarTower O D (AlgebraicClosure Kv) :=
  IsScalarTower.of_algebraMap_eq' rfl

set_option maxHeartbeats 1000000 in
-- Comparing the nested arithmetic Hopf structures needs additional elaboration time.
/-- The previously constructed point bijection preserves the descended addition. -/
theorem localUnramifiedTwistPoints_add (x y : X.Points) :
    localUnramifiedTwistPoints v p X he χ hc hχ (x + y) =
      (Algebra.TensorProduct.lift (localUnramifiedTwistPoints v p X he χ hc hχ x)
        (localUnramifiedTwistPoints v p X he χ hc hχ y) (fun _ _ ↦ .all _ _)).comp
          (twistComul σ τ (localUnramifiedTwistAction_hopf v p X he χ hc)
            (finiteCharacter_twistTensorMap_bijective v χ hc X.CoordinateRing X.CoordinateRing
              τ τ hχ)) := by
  have hp (z : X.Points) : localUnramifiedTwistPoints v p X he χ hc hχ z =
      twistPoint σ τ (IsScalarTower.toAlgHom O D (AlgebraicClosure Kv)) (X.integralPoints z) :=
    finiteCharacterTwistPointsEquiv_apply v χ hc X.CoordinateRing τ hχ _ (X.integralPoints z)
  let d := twistComul σ τ (localUnramifiedTwistAction_hopf v p X he χ hc)
    (finiteCharacter_twistTensorMap_bijective v χ hc X.CoordinateRing X.CoordinateRing τ τ hχ)
  refine (hp (x + y)).trans ?_
  refine (congrArg (twistPoint σ τ (IsScalarTower.toAlgHom O D (AlgebraicClosure Kv)))
    (FF.integralPoints_add X x y)).trans ?_
  refine (twistPoint_comul σ τ (localUnramifiedTwistAction_hopf v p X he χ hc)
    (IsScalarTower.toAlgHom O D (AlgebraicClosure Kv))
    (finiteCharacter_twistTensorMap_bijective v χ hc X.CoordinateRing X.CoordinateRing τ τ hχ)
    (X.integralPoints x) (X.integralPoints y)).symm.trans ?_
  exact congrArg₂ (fun f g ↦ (Algebra.TensorProduct.lift f g (fun _ _ ↦ .all _ _)).comp d)
    (hp x).symm (hp y).symm

/-- The actual finite-flat twist's group of points is the original group. -/
def localUnramifiedTwistPointAddEquiv :
    X.Points ≃+ (localUnramifiedTwistModel v p X he χ hc hχ).Points where
  toEquiv := (localUnramifiedTwistPoints v p X he χ hc hχ).trans
    (localUnramifiedTwistModel v p X he χ hc hχ).integralPoints.symm
  map_add' x y := by
    let Y := localUnramifiedTwistModel v p X he χ hc hχ
    apply Y.integralPoints.injective
    have hx := Y.integralPoints.apply_symm_apply (localUnramifiedTwistPoints v p X he χ hc hχ x)
    have hy := Y.integralPoints.apply_symm_apply (localUnramifiedTwistPoints v p X he χ hc hχ y)
    have hxy := Y.integralPoints.apply_symm_apply
      (localUnramifiedTwistPoints v p X he χ hc hχ (x + y))
    refine hxy.trans ((localUnramifiedTwistPoints_add v p X he χ hc hχ x y).trans ?_)
    refine Eq.trans ?_ (FF.integralPoints_add Y _ _).symm
    exact congrArg₂ (fun f g ↦ (Algebra.TensorProduct.lift f g (fun _ _ ↦ .all _ _)).comp
      (Bialgebra.comulAlgHom O Y.CoordinateRing)) hx.symm hy.symm

/-- The finite-flat twist has the required inverse-character action on its actual points. -/
theorem localUnramifiedTwistPointAddEquiv_equivariant
    (γ : Field.absoluteGaloisGroup Kv) (x : X.Points) :
    γ • localUnramifiedTwistPointAddEquiv v p X he χ hc hχ x =
      localUnramifiedTwistPointAddEquiv v p X he χ hc hχ ((↑(χ γ)⁻¹ : k) • (γ • x)) := by
  let Y := localUnramifiedTwistModel v p X he χ hc hχ
  apply Y.integralPoints.injective
  have hx := Y.integralPoints.apply_symm_apply (localUnramifiedTwistPoints v p X he χ hc hχ x)
  have hz := Y.integralPoints.apply_symm_apply
    (localUnramifiedTwistPoints v p X he χ hc hχ ((↑(χ γ)⁻¹ : k) • (γ • x)))
  refine (FF.integralPoints_smul Y γ _).trans ?_
  exact (congrArg (fun f ↦ (γ.toAlgHom.restrictScalars O).comp f) hx).trans
    ((localUnramifiedTwistPoints_equivariant v p X he χ hc hχ γ x).trans hz.symm)

end ThreeAdicPlan
