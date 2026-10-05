/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.AbsoluteGaloisGroup.UnramifiedCharacterTensor
public import FLT.GroupScheme.CharacterIntegralFixedScalars
public import FLT.GroupScheme.TwistHopfDescent

/-!
# Hopf descent over the unramified character splitting ring

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

/-- The splitting integers act on the chosen algebraic closure through their fraction field. -/
local instance characterHopfClosureAlgebra : Algebra D (AlgebraicClosure Kv) :=
  ((algebraMap L (AlgebraicClosure Kv)).comp (algebraMap D L)).toAlgebra

/-- The splitting-integer and original-integer scalar actions agree. -/
local instance characterHopfClosureTower : IsScalarTower O D (AlgebraicClosure Kv) :=
  IsScalarTower.of_algebraMap_eq' rfl

/-- The actual invariant coordinates form a Hopf algebra over the original integral base. -/
@[instance_reducible]
def finiteCharacterTwistHopf : HopfAlgebra O (twistModel σ τ) := by
  let hf := finiteCharacter_twist_finite_free v χ hc H τ
  let : Module.Free O (twistModel σ τ) := hf.2
  let : Module.Flat O (twistModel σ τ) := Module.Flat.of_free
  let := finiteCharacter_twist_generic_etale v χ hc H τ hχ
  apply twistHopf (K := Kv) (Ω := AlgebraicClosure Kv) σ τ hτ
    (finiteCharacter_twistTensorMap_bijective v χ hc H H τ τ hχ)
    (finiteCharacter_scalar_injective v χ hc) (finiteCharacter_fixed_scalars v χ hc)
    (IsScalarTower.toAlgHom O D (AlgebraicClosure Kv))
  intro f
  obtain ⟨g, hg⟩ := (finiteCharacterTwistPointsEquiv v χ hc H τ hχ
    (AlgebraicClosure Kv)).surjective f
  refine ⟨g, ?_⟩
  rwa [finiteCharacterTwistPointsEquiv_apply] at hg

end LocalRamification
