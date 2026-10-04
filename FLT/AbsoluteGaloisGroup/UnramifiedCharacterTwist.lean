/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.AbsoluteGaloisGroup.UnramifiedCharacterAlgebraDescent
public import FLT.GroupScheme.SemilinearTwistPoints
public import Mathlib.RingTheory.Etale.Descent

/-!
# Integral twists on the actual unramified character splitting ring

For an integral coordinate action of the character's finite splitting group,
the simultaneous tensor action constructs fixed coordinates, proves finite
freeness and recovers the original algebra after faithfully flat base change.
Coefficient evaluation identifies its points and has the prescribed inverse
action. Integral coefficient actions and descended Hopf operations still
require separate construction for the ordinary quotient-twist application.
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
attribute [local instance] finiteLevel_finiteDimensional finiteLevel_isDVR
local notation "σ" => MulSemiringAction.toAlgAut Gal(L/Kv) O D

variable (H : Type) [CommRing H] [Algebra (v.adicCompletionIntegers K) H]
  (τ : ((openNormalFixedField (characterOpenNormal v χ hc)) ≃ₐ[v.adicCompletion K]
    (openNormalFixedField (characterOpenNormal v χ hc))) →*
      (H ≃ₐ[v.adicCompletionIntegers K] H))
  (hχ : localInertiaGroup v ≤ χ.ker)

/-- Effective recovery of the twist over the actual integral splitting coefficients. -/
def finiteCharacterTwistEquiv : D ⊗[O] twistModel σ τ ≃ₐ[D] D ⊗[O] H where
  __ := (finiteCharacterAlgebraEquiv v χ hc (D ⊗[O] H) (twistAction σ τ)
    (twistAction_coefficients σ τ) hχ).toRingEquiv
  commutes' s := by
    change algebraMap D (D ⊗[O] H) s * 1 = algebraMap D (D ⊗[O] H) s
    exact mul_one _

/-- Recovery is coefficient multiplication on pure tensors. -/
theorem finiteCharacterTwistEquiv_tmul (s : D) (x : twistModel σ τ) :
    finiteCharacterTwistEquiv v χ hc H τ hχ (s ⊗ₜ[O] x) =
      (s ⊗ₜ[O] (1 : H)) * x.val := rfl

/-- The constructed integral twist coordinates are finite free. -/
theorem finiteCharacter_twist_finite_free [Module.Finite O H] [Module.Flat O H] :
    Module.Finite O (twistModel σ τ) ∧ Module.Free O (twistModel σ τ) :=
  finiteCharacter_fixed_finite_free v χ hc (D ⊗[O] H) (twistAction σ τ)

include hχ in
/-- Etaleness of the original generic fibre descends to the constructed twist coordinates. -/
theorem finiteCharacter_twist_generic_etale [Algebra.Etale Kv (Kv ⊗[O] H)] :
    Algebra.Etale Kv (Kv ⊗[O] twistModel σ τ) := by
  let := finiteCharacter_integers_faithfullyFlat v χ hc
  let T := Kv ⊗[O] D
  let : Algebra D T := Algebra.TensorProduct.rightAlgebra
  let : IsScalarTower O D T := Algebra.TensorProduct.right_isScalarTower
  let eT : T ⊗[O] twistModel σ τ ≃ₐ[T] T ⊗[O] H :=
    (Algebra.TensorProduct.cancelBaseChange O D T T (twistModel σ τ)).symm.trans
      ((Algebra.TensorProduct.congr AlgEquiv.refl
        (finiteCharacterTwistEquiv v χ hc H τ hχ)).trans
          (Algebra.TensorProduct.cancelBaseChange O D T T H))
  let e : T ⊗[Kv] (Kv ⊗[O] twistModel σ τ) ≃ₐ[T] T ⊗[Kv] (Kv ⊗[O] H) :=
    (Algebra.TensorProduct.cancelBaseChange O Kv T T (twistModel σ τ)).trans
      (eT.trans (Algebra.TensorProduct.cancelBaseChange O Kv T T H).symm)
  let : Algebra.Etale T (T ⊗[Kv] (Kv ⊗[O] twistModel σ τ)) :=
    Algebra.Etale.of_equiv e.symm
  exact Algebra.Etale.of_etale_tensorProduct_of_faithfullyFlat T

variable (Ω : Type) [CommRing Ω] [Algebra (v.adicCompletionIntegers K) Ω]
  [Algebra (IntegralClosure (v.adicCompletionIntegers K)
    (openNormalFixedField (characterOpenNormal v χ hc))) Ω]
  [IsScalarTower (v.adicCompletionIntegers K)
    (IntegralClosure (v.adicCompletionIntegers K)
      (openNormalFixedField (characterOpenNormal v χ hc))) Ω]

/-- Choosing the splitting coefficients gives a bijection of geometric algebra points. -/
def finiteCharacterTwistPointsEquiv : (H →ₐ[O] Ω) ≃ (twistModel σ τ →ₐ[O] Ω) :=
  (Algebra.TensorProduct.liftEquivRight O D H Ω).trans
    ((AlgEquiv.arrowCongr (finiteCharacterTwistEquiv v χ hc H τ hχ).symm
      AlgEquiv.refl).trans (Algebra.TensorProduct.liftEquivRight O D (twistModel σ τ) Ω).symm)

/-- The point bijection is the specified coefficient evaluation map. -/
theorem finiteCharacterTwistPointsEquiv_apply (f : H →ₐ[O] Ω) :
    finiteCharacterTwistPointsEquiv v χ hc H τ hχ Ω f =
      twistPoint σ τ (IsScalarTower.toAlgHom O D Ω) f := by
  ext x
  change Algebra.TensorProduct.lift (Algebra.ofId D Ω) f (fun _ _ ↦ .all _ _)
    (finiteCharacterTwistEquiv v χ hc H τ hχ (1 ⊗ₜ[O] x)) = _
  rw [finiteCharacterTwistEquiv_tmul]
  simp only [← Algebra.TensorProduct.one_def, one_mul]
  rfl

set_option maxHeartbeats 1000000 in
-- Integral closure and nested tensor actions require additional elaboration time.
/-- The point bijection intertwines the specified coefficient and inverse twist actions. -/
theorem finiteCharacterTwistPointsEquiv_equivariant (f : H →ₐ[O] Ω)
    (γ : Ω →ₐ[O] Ω) (g : Gal(L/Kv))
    (hγ : γ.comp (IsScalarTower.toAlgHom O D Ω) =
      (IsScalarTower.toAlgHom O D Ω).comp (σ g).toAlgHom) :
    γ.comp (finiteCharacterTwistPointsEquiv v χ hc H τ hχ Ω f) =
      finiteCharacterTwistPointsEquiv v χ hc H τ hχ Ω
        ((γ.comp f).comp (τ g⁻¹).toAlgHom) := by
  rw [finiteCharacterTwistPointsEquiv_apply, finiteCharacterTwistPointsEquiv_apply]
  exact twistPoint_equivariant σ τ _ f γ g hγ

end LocalRamification
