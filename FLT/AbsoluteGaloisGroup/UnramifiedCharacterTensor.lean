/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.AbsoluteGaloisGroup.UnramifiedCharacterTwist
public import FLT.GroupScheme.ScalarRecoveryOverlap
public import FLT.GroupScheme.TwistTensorRecovery
public import FLT.GroupScheme.TwistTensorCoherence

/-!
# Tensor descent over the actual unramified splitting ring

Trivial inertia supplies all scalar recovery hypotheses for the fixed-algebra
tensor comparison. Thus the comparison is an isomorphism on the original
integral base, with the triple coherence of `twistTensorMap_assoc`.
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
variable (H J : Type) [CommRing H] [CommRing J]
  [Algebra (v.adicCompletionIntegers K) H] [Algebra (v.adicCompletionIntegers K) J]
  (τ : ((openNormalFixedField (characterOpenNormal v χ hc)) ≃ₐ[v.adicCompletion K]
    (openNormalFixedField (characterOpenNormal v χ hc))) →*
      (H ≃ₐ[v.adicCompletionIntegers K] H))
  (υ : ((openNormalFixedField (characterOpenNormal v χ hc)) ≃ₐ[v.adicCompletion K]
    (openNormalFixedField (characterOpenNormal v χ hc))) →*
      (J ≃ₐ[v.adicCompletionIntegers K] J))
  (hχ : localInertiaGroup v ≤ χ.ker)

include hχ in
/-- Tensor descent for the actual splitting integral closure of the character. -/
theorem finiteCharacter_twistTensorMap_bijective :
    Function.Bijective (twistTensorMap σ τ υ) := by
  let := finiteCharacter_integers_faithfullyFlat v χ hc
  apply twistTensorMap_bijective
  · exact finiteCharacter_algebra_recovery v χ hc _ _ (twistAction_coefficients σ τ) hχ
  · exact finiteCharacter_algebra_recovery v χ hc _ _ (twistAction_coefficients σ υ) hχ
  · exact finiteCharacter_algebra_recovery v χ hc _ _
      (twistAction_coefficients σ (twistAction τ υ)) hχ

/-- The canonical fixed tensor comparison over the original arithmetic base. -/
def finiteCharacterTwistTensorEquiv :
    twistModel σ τ ⊗[O] twistModel σ υ ≃ₐ[O] twistModel σ (twistAction τ υ) :=
  AlgEquiv.ofBijective (twistTensorMap σ τ υ)
    (finiteCharacter_twistTensorMap_bijective v χ hc H J τ υ hχ)

/-- The arithmetic equivalence uses the same coefficient-multiplication comparison. -/
theorem finiteCharacterTwistTensorEquiv_tmul (x : twistModel σ τ) (y : twistModel σ υ) :
    (finiteCharacterTwistTensorEquiv v χ hc H J τ υ hχ (x ⊗ₜ[O] y)).val =
      tensorJoin x.val y.val := rfl

/-- The actual scalar recoveries give the transition between any two splitting embeddings. -/
def finiteCharacterTwistOverlap (T : Type) [CommRing T] [Algebra O T]
    (a b : D →ₐ[O] T) : T ⊗[O] H ≃ₐ[T] T ⊗[O] H :=
  recoveryOverlap (finiteCharacterTwistEquiv v χ hc H τ hχ) a b

/-- The actual arithmetic transitions satisfy the overlap cocycle. -/
theorem finiteCharacterTwistOverlap_cocycle (T : Type) [CommRing T] [Algebra O T]
    (a b c : D →ₐ[O] T) :
    (finiteCharacterTwistOverlap v χ hc H τ hχ T a b).trans
      (finiteCharacterTwistOverlap v χ hc H τ hχ T b c) =
        finiteCharacterTwistOverlap v χ hc H τ hχ T a c :=
  recoveryOverlap_cocycle (finiteCharacterTwistEquiv v χ hc H τ hχ) a b c

/-- The cocycle holds on the actual threefold tensor overlap of the integral splitting ring. -/
theorem finiteCharacterTwistOverlap_triple :
    (finiteCharacterTwistOverlap v χ hc H τ hχ ((D ⊗[O] D) ⊗[O] D)
      tripleOverlapLeft tripleOverlapMiddle).trans
        (finiteCharacterTwistOverlap v χ hc H τ hχ ((D ⊗[O] D) ⊗[O] D)
          tripleOverlapMiddle tripleOverlapRight) =
      finiteCharacterTwistOverlap v χ hc H τ hχ ((D ⊗[O] D) ⊗[O] D)
        tripleOverlapLeft tripleOverlapRight :=
  recoveryOverlap_triple (finiteCharacterTwistEquiv v χ hc H τ hχ)

end LocalRamification
