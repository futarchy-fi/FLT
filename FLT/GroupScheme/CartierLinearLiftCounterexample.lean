/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.CartierLinearEvaluationBase
public import FLT.GroupScheme.CartierLinearLiftCounterexampleData
public import FLT.GroupScheme.SquareZeroPointLift

/-! # Linear character lifts do not satisfy the proposed convolution power identity

The constant group of order two over ZMod 16 has an algebra-valued generator.
Its canonical doubled lift is the augmentation. A genuine dual character modulo
8 sends the generator to 3, and the square of its linear lift is 9 modulo 16.
Thus square-zero reduction and annihilation of its kernel do not imply the
power identity for arbitrary linear coefficient lifts.
-/

@[expose] public noncomputable section
namespace HopfAlgebra.CartierDual.LinearLiftCounterexample

/-- The reduced original point is genuinely killed by the specified exponent. -/
theorem reduced_generator_square :
    (WithConv.toConv (quotientMap.comp generator) ^ 2).ofConv =
      (1 : WithConv (Coordinates →ₐ[ZMod 16] ZMod 8)).ofConv := by
  apply AlgHom.toLinearMap_injective
  have h := congrArg AlgHom.toLinearMap generator_square
  have h' := congrArg (fun f ↦ quotientMap.toLinearMap.comp f) h
  have hp : (WithConv.toConv generator ^ 2).ofConv.toLinearMap =
      (WithConv.toConv generator.toLinearMap ^ 2).ofConv :=
    congrArg WithConv.ofConv (AlgHom.toLinearMap_convPow (WithConv.toConv generator) 2)
  rw [hp, algHom_comp_linear_convPow] at h'
  have hpq : (WithConv.toConv (quotientMap.comp generator) ^ 2).ofConv.toLinearMap =
      (WithConv.toConv (quotientMap.comp generator).toLinearMap ^ 2).ofConv :=
    congrArg WithConv.ofConv
      (AlgHom.toLinearMap_convPow (WithConv.toConv (quotientMap.comp generator)) 2)
  rw [hpq]
  exact h'

/-- Canonical multiplication lifting sends this original point to the augmentation. -/
theorem canonical_generator_lift :
    squareZeroPointLift quotientMap quotientMap_surjective quotientMap_kernel_square
      2 quotientMap_kernel_two (quotientMap.comp generator) =
        (1 : WithConv (Coordinates →ₐ[ZMod 16] ZMod 16)).ofConv := by
  rw [squareZeroPointLift_eq_of_algHom _ _ _ _ _ _ generator rfl]
  exact generator_square

/-- The proposed identity fails with genuine algebra points and verified linear lifts. -/
theorem linear_convolution_identity_fails :
    linearTestEvaluation liftedCharacter
      ((squareZeroPointLift quotientMap quotientMap_surjective quotientMap_kernel_square
        2 quotientMap_kernel_two (quotientMap.comp generator)).toLinearMap -
          (1 : WithConv (Coordinates →ₐ[ZMod 16] ZMod 16)).ofConv.toLinearMap) ≠
      (linearTestEvaluation liftedCharacter generator.toLinearMap) ^ 2 - 1 := by
  rw [canonical_generator_lift, sub_self, map_zero, linearTestEvaluation_base,
    liftedCharacter_generator]
  decide

/-- An algebra lift of the reduced dual character would contradict its order-two relation. -/
theorem reducedCharacter_has_no_algebra_lift :
    ¬ ∃ χ : CartierDual (ZMod 16) Coordinates →ₐ[ZMod 16] ZMod 16,
      quotientMap.comp χ = reducedCharacter := by
  rintro ⟨χ, hχ⟩
  let e := bidualAlgEquiv (R := ZMod 16) (A := GroupRing)
  let g : GroupRing := MonoidAlgebra.single (Multiplicative.ofAdd 1 : Group) 1
  have hg : g ^ 2 = 1 := by
    change MonoidAlgebra.single _ _ ^ 2 = _
    rw [MonoidAlgebra.single_pow]
    rfl
  have hs : (χ (e g)) ^ 2 = 1 := by rw [← map_pow, ← map_pow, hg, map_one, map_one]
  have hq : quotientMap (χ (e g)) = 3 := by
    have h := AlgHom.congr_fun hχ (e g)
    change quotientMap (χ (e g)) = reducedCharacter.toLinearMap (e g) at h
    rw [← liftedCharacter_reduction] at h
    have he : e g = WithConv.toConv generator.toLinearMap := generator_linear.symm
    simp only [LinearMap.comp_apply, he, liftedCharacter_generator] at h
    exact h
  have hn : ∀ a : ZMod 16, quotientMap a = 3 → a ^ 2 ≠ 1 := by decide
  exact hn _ hq hs

end HopfAlgebra.CartierDual.LinearLiftCounterexample
