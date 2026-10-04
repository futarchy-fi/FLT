/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.AbsoluteGaloisGroup.UnramifiedCharacterHopf
public import FLT.GroupScheme.TwistHopfComparison
public import FLT.GroupScheme.TwistHopfScalarRecovery

/-!
# Group comparison for the arithmetic Hopf twist

The actual fixed coordinate ring receives a Hopf structure from integral
Galois descent. All tensor, scalar and generic-point recovery hypotheses
are discharged for the actual character splitting extension.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open NumberField IsLocalRing GaloisRepresentation.Extensions SemilinearDescent
open scoped TensorProduct
namespace LocalRamification
variable {K : Type} [Field K] [NumberField K]
  (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
local notation "Kv" => v.adicCompletion K
local notation "O" => v.adicCompletionIntegers K
variable {k : Type} [Field k] [TopologicalSpace k] [DiscreteTopology k]
  (χ : Field.absoluteGaloisGroup (v.adicCompletion K) →* kˣ) (hc : Continuous χ)
local notation "L" => openNormalFixedField (characterOpenNormal v χ hc)
local notation "D" => IntegralClosure O L
local notation "σ" => MulSemiringAction.toAlgAut Gal(L/Kv) O D
variable (H : Type) [CommRing H] [HopfAlgebra (v.adicCompletionIntegers K) H]
  [Module.Finite (v.adicCompletionIntegers K) H]
  [Module.Flat (v.adicCompletionIntegers K) H]
  [Algebra.Etale (v.adicCompletion K) ((v.adicCompletion K) ⊗[v.adicCompletionIntegers K] H)]
  (τ : ((openNormalFixedField (characterOpenNormal v χ hc)) ≃ₐ[v.adicCompletion K]
    (openNormalFixedField (characterOpenNormal v χ hc))) →*
      (H ≃ₐ[v.adicCompletionIntegers K] H))
  (hτ : ∀ g, ∃ f : H →ₐc[v.adicCompletionIntegers K] H, f.toAlgHom = (τ g).toAlgHom)
  (hχ : localInertiaGroup v ≤ χ.ker)

/-- The splitting integers embed in the algebraic closure used for point comparison. -/
local instance characterComparisonClosureAlgebra : Algebra D (AlgebraicClosure Kv) :=
  ((algebraMap L (AlgebraicClosure Kv)).comp (algebraMap D L)).toAlgebra

/-- The point comparison uses the original integral scalar tower. -/
local instance characterComparisonClosureTower : IsScalarTower O D (AlgebraicClosure Kv) :=
  IsScalarTower.of_algebraMap_eq' rfl

/-- The arithmetic twist of a cocommutative Hopf algebra is cocommutative. -/
theorem finiteCharacterTwistIsCocomm [Coalgebra.IsCocomm O H] :
    letI := finiteCharacterTwistHopf v χ hc H τ hτ hχ
    Coalgebra.IsCocomm O (twistModel σ τ) := by
  let hf := finiteCharacter_twist_finite_free v χ hc H τ
  let : Module.Free O (twistModel σ τ) := hf.2
  let : Module.Flat O (twistModel σ τ) := Module.Flat.of_free
  let := finiteCharacter_twist_generic_etale v χ hc H τ hχ
  exact twistIsCocomm (K := Kv) (Ω := AlgebraicClosure Kv) σ τ hτ
    (finiteCharacter_twistTensorMap_bijective v χ hc H H τ τ hχ)
    (finiteCharacter_scalar_injective v χ hc) (finiteCharacter_fixed_scalars v χ hc)
    (IsScalarTower.toAlgHom O D (AlgebraicClosure Kv)) (by
      intro f
      obtain ⟨g, hg⟩ := (finiteCharacterTwistPointsEquiv v χ hc H τ hχ
        (AlgebraicClosure Kv)).surjective f
      refine ⟨g, ?_⟩
      rwa [finiteCharacterTwistPointsEquiv_apply] at hg)

/-- Actual arithmetic point recovery preserves the full convolution group law. -/
def finiteCharacterTwistPointMulEquiv :
    letI := finiteCharacterTwistHopf v χ hc H τ hτ hχ
    WithConv (H →ₐ[O] AlgebraicClosure Kv) ≃*
      WithConv (twistModel σ τ →ₐ[O] AlgebraicClosure Kv) := by
  let hf := finiteCharacter_twist_finite_free v χ hc H τ
  let : Module.Free O (twistModel σ τ) := hf.2
  let : Module.Flat O (twistModel σ τ) := Module.Flat.of_free
  let := finiteCharacter_twist_generic_etale v χ hc H τ hχ
  have hp : Function.Bijective (twistPoint σ τ
      (IsScalarTower.toAlgHom O D (AlgebraicClosure Kv))) := by
    have he : (finiteCharacterTwistPointsEquiv v χ hc H τ hχ (AlgebraicClosure Kv) :
        (H →ₐ[O] AlgebraicClosure Kv) → _) =
        twistPoint σ τ (IsScalarTower.toAlgHom O D (AlgebraicClosure Kv)) :=
      funext (finiteCharacterTwistPointsEquiv_apply v χ hc H τ hχ (AlgebraicClosure Kv))
    exact he ▸ (finiteCharacterTwistPointsEquiv v χ hc H τ hχ (AlgebraicClosure Kv)).bijective
  exact twistPointMulEquiv (K := Kv) σ τ hτ
    (finiteCharacter_twistTensorMap_bijective v χ hc H H τ τ hχ)
    (finiteCharacter_scalar_injective v χ hc) (finiteCharacter_fixed_scalars v χ hc)
    (IsScalarTower.toAlgHom O D (AlgebraicClosure Kv)) hp.2 hp.1

/-- Recovery over the actual splitting ring preserves the full Hopf structure. -/
def finiteCharacterTwistHopfRecovery :
    letI := finiteCharacterTwistHopf v χ hc H τ hτ hχ
    D ⊗[O] twistModel σ τ ≃ₐc[D] D ⊗[O] H := by
  let hf := finiteCharacter_twist_finite_free v χ hc H τ
  let : Module.Free O (twistModel σ τ) := hf.2
  let : Module.Flat O (twistModel σ τ) := Module.Flat.of_free
  let := finiteCharacter_twist_generic_etale v χ hc H τ hχ
  have hp : Function.Bijective (twistPoint σ τ
      (IsScalarTower.toAlgHom O D (AlgebraicClosure Kv))) := by
    have he : (finiteCharacterTwistPointsEquiv v χ hc H τ hχ (AlgebraicClosure Kv) :
        (H →ₐ[O] AlgebraicClosure Kv) → _) =
        twistPoint σ τ (IsScalarTower.toAlgHom O D (AlgebraicClosure Kv)) :=
      funext (finiteCharacterTwistPointsEquiv_apply v χ hc H τ hχ (AlgebraicClosure Kv))
    exact he ▸ (finiteCharacterTwistPointsEquiv v χ hc H τ hχ (AlgebraicClosure Kv)).bijective
  exact twistHopfRecovery (K := Kv) σ τ hτ
    (finiteCharacter_twistTensorMap_bijective v χ hc H H τ τ hχ)
    (finiteCharacter_scalar_injective v χ hc) (finiteCharacter_fixed_scalars v χ hc)
    (IsScalarTower.toAlgHom O D (AlgebraicClosure Kv)) hp.2
    (finiteCharacter_algebra_recovery v χ hc _ _ (twistAction_coefficients σ τ) hχ)

end LocalRamification
