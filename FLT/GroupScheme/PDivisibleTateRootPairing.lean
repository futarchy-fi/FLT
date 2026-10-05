/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.PDivisibleFiniteRootPairing
public import FLT.GroupScheme.PDivisibleTateEvaluationSurjective

/-! # The original bilinear Tate pairing with its genuine coherent-root target -/

@[expose] public noncomputable section
namespace ThreeAdicPlan.PDivisibleSystem
variable {R K : Type} [CommRing R] [IsLocalRing R] [Field K] [Algebra R K]
  [IsDomain R] [IsPrincipalIdealRing R] [IsFractionRing R K] [CharZero K]
  {p height : ℕ} [Fact p.Prime] (X : PDivisibleSystem R K p height)

/-- Pairing with an actual dual vector is linear into the actual cyclotomic root module. -/
def tateRootPairingRight (y : X.CartierTate) :
    X.tateSequences →ₗ[ℤ_[p]] TateRootModule (AlgebraicClosure K) p where
  toFun x := ⟨fun n ↦ X.finiteRootPairing n (X.cartierTateEval n y) (X.tateEvalLinear n x), by
    intro m n h
    apply Additive.toMul.injective
    apply Subtype.ext
    exact X.cartierTatePairing_transition h y x⟩
  map_add' x z := by
    apply Subtype.ext
    funext n
    exact ((X.finiteRootPairing n (X.cartierTateEval n y)).comp
      (X.tateEvalLinear n)).map_add x z
  map_smul' a x := by
    apply Subtype.ext
    funext n
    exact ((X.finiteRootPairing n (X.cartierTateEval n y)).comp
      (X.tateEvalLinear n)).map_smul a x

/-- The bilinear map retains both original Tate modules and the actual roots of unity. -/
def tateRootPairing : X.CartierTate →ₗ[ℤ_[p]]
    (X.tateSequences →ₗ[ℤ_[p]] TateRootModule (AlgebraicClosure K) p) where
  toFun := X.tateRootPairingRight
  map_add' y z := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    funext n
    exact LinearMap.congr_fun (((X.finiteRootPairing n).comp
      (X.cartierTateEval n)).map_add y z) (X.tateEvalLinear n x)
  map_smul' a y := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    funext n
    exact LinearMap.congr_fun (((X.finiteRootPairing n).comp
      (X.cartierTateEval n)).map_smul a y) (X.tateEvalLinear n x)

/-- The new linear packaging evaluates to exactly the previously constructed Cartier roots. -/
theorem tateRootPairing_value (y : X.CartierTate) (x : X.tateSequences) (n : ℕ) :
    tateRootValue (AlgebraicClosure K) p n
      (tateRootEval (AlgebraicClosure K) p n (X.tateRootPairing y x)) =
        Additive.ofMul (X.cartierTatePairing y x n) := rfl

/-- The root-valued linear map is injective by the original finite Cartier evaluations. -/
theorem tateRootPairing_injective : Function.Injective X.tateRootPairing := by
  intro y z h
  apply X.cartierTatePairing_separates
  intro x n
  exact congrArg (fun f : X.tateSequences →ₗ[ℤ_[p]] TateRootModule (AlgebraicClosure K) p ↦
    (tateRootValue (AlgebraicClosure K) p n (tateRootEval (AlgebraicClosure K) p n (f x))).toMul) h
end ThreeAdicPlan.PDivisibleSystem
