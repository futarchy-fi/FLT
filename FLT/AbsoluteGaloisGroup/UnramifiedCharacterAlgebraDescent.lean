/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.AbsoluteGaloisGroup.UnramifiedCharacterIntegers
public import FLT.GroupScheme.ResidueGaloisCoordinates
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra

/-!
# Effective algebra descent over the character's integral splitting ring

The coefficient ring is the integral closure in the actual open-kernel field.
Its trivial inertia supplies integral Galois coordinates, so every compatible
semilinear algebra action descends effectively. Finite flat algebras descend
to finite free coordinates. Descent of Hopf operations is not asserted here.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open NumberField IsLocalRing GaloisRepresentation.Extensions
open scoped TensorProduct
namespace LocalRamification
variable {K : Type} [Field K] [NumberField K]
  (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
local notation "Kv" => v.adicCompletion K
local notation "O" => v.adicCompletionIntegers K
variable {k : Type} [Field k] [TopologicalSpace k] [DiscreteTopology k]
  (χ : Field.absoluteGaloisGroup (v.adicCompletion K) →* kˣ) (hc : Continuous χ)
local notation "N" => characterOpenNormal v χ hc
local notation "L" => openNormalFixedField N
local notation "D" => IntegralClosure O L
attribute [local instance] finiteLevel_finiteDimensional finiteLevel_isDVR

local instance characterDescentFraction : IsFractionRing D L := by
  change IsFractionRing (integralClosure O L) L
  exact integralClosure.isFractionRing_of_finite_extension Kv L

local instance characterDescentDistrib : SMulDistribClass Gal(L/Kv) D L :=
  ⟨fun g b l ↦ by
    simp only [Algebra.smul_def, smul_mul', mul_eq_mul_right_iff]
    left
    rfl⟩

local instance characterDescentGalois : IsGaloisGroup Gal(L/Kv) O D :=
  IsGaloisGroup.of_isFractionRing Gal(L/Kv) O D Kv L

local instance characterDescentDedekind : IsDedekindDomain O :=
  IsPrincipalIdealRing.isDedekindDomain _

/-- The actual integral splitting extension is faithfully flat. -/
theorem finiteCharacter_integers_faithfullyFlat : Module.FaithfullyFlat O D := by
  let : Module.IsTorsionFree O D := by
    rw [Module.isTorsionFree_iff_faithfulSMul, faithfulSMul_iff_algebraMap_injective]
    intro x y hxy
    apply Subtype.ext
    apply (algebraMap Kv L).injective
    exact congrArg Subtype.val hxy
  infer_instance

variable (B : Type) [CommRing B] [Algebra (v.adicCompletionIntegers K) B]
  [Algebra (IntegralClosure (v.adicCompletionIntegers K)
    (openNormalFixedField (characterOpenNormal v χ hc))) B]
  [IsScalarTower (v.adicCompletionIntegers K)
    (IntegralClosure (v.adicCompletionIntegers K)
      (openNormalFixedField (characterOpenNormal v χ hc))) B]
  (ρ : ((openNormalFixedField (characterOpenNormal v χ hc)) ≃ₐ[v.adicCompletion K]
    (openNormalFixedField (characterOpenNormal v χ hc))) →*
    (B ≃ₐ[v.adicCompletionIntegers K] B))
  (hρ : ∀ g s, ρ g (algebraMap (IntegralClosure (v.adicCompletionIntegers K)
    (openNormalFixedField (characterOpenNormal v χ hc))) B s) =
    algebraMap (IntegralClosure (v.adicCompletionIntegers K)
      (openNormalFixedField (characterOpenNormal v χ hc))) B (g • s))
  (hχ : localInertiaGroup v ≤ χ.ker)

include hρ hχ in
/-- The actual unramified character extension makes semilinear algebra descent effective. -/
theorem finiteCharacter_algebra_recovery :
    Function.Bijective (SemilinearDescent.recoveryMap (S := D) ρ) := by
  let := finiteCharacter_integers_faithfullyFlat v χ hc
  exact SemilinearDescent.unramified_recoveryMap_bijective ρ hρ
    (finiteCharacter_inertia_eq_bot v χ hc hχ)

/-- The descended integral algebra recovers the given one on the actual splitting base. -/
def finiteCharacterAlgebraEquiv : D ⊗[O] SemilinearDescent.fixed ρ ≃ₐ[O] B :=
  AlgEquiv.ofBijective (SemilinearDescent.recoveryMap ρ)
    (finiteCharacter_algebra_recovery v χ hc B ρ hρ hχ)

/-- Finite flat ambient coordinates give finite free descended integral coordinates. -/
theorem finiteCharacter_fixed_finite_free [Module.Finite D B] [Module.Flat D B] :
    Module.Finite O (SemilinearDescent.fixed ρ) ∧
      Module.Free O (SemilinearDescent.fixed ρ) := by
  let := finiteCharacter_integers_finite v χ hc
  let := finiteCharacter_integers_faithfullyFlat v χ hc
  let : Module.Finite O B := Module.Finite.trans D B
  let := Module.Flat.trans O D B
  let := SemilinearDescent.fixed_finiteFlat ρ
  exact ⟨inferInstance, SemilinearDescent.fixed_free ρ⟩

end LocalRamification
