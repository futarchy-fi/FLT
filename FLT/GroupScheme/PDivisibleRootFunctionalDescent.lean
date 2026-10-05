/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.PDivisibleTateRootPairing
public import FLT.GroupScheme.PDivisibleTateReduction

/-! # Finite-level descent of actual coherent-root-valued functionals -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace ThreeAdicPlan.PDivisibleSystem
variable {R K : Type} [CommRing R] [IsLocalRing R] [Field K] [Algebra R K]
  [IsDomain R] [IsPrincipalIdealRing R] [IsFractionRing R K] [CharZero K]
  {p height : ℕ} [Fact p.Prime] (X : PDivisibleSystem R K p height)
  (f : X.tateSequences →ₗ[ℤ_[p]] TateRootModule (AlgebraicClosure K) p)

omit [IsDomain R] [IsPrincipalIdealRing R] in
/-- The nth root evaluation kills precisely the divisibility needed to descend f. -/
theorem rootFunctional_ker_le (n : ℕ) :
    LinearMap.ker (X.tateEvalLinear n) ≤
      LinearMap.ker ((tateRootEval (AlgebraicClosure K) p n).comp f) := by
  intro x hx
  obtain ⟨y, rfl⟩ := (X.tateEvalLinear_eq_zero_iff n x).mp hx
  change tateRootEval (AlgebraicClosure K) p n (f (p ^ n • y)) = 0
  rw [map_nsmul, map_nsmul]
  exact tateRootLevel_killed _ _ n _

/-- Descend the actual functional to the original nth finite group. -/
def rootFunctionalLevel (n : ℕ) :
    (X.level n).Points →ₗ[ℤ_[p]] TateRootLevel (AlgebraicClosure K) p n :=
  ((LinearMap.ker (X.tateEvalLinear n)).liftQ
    ((tateRootEval (AlgebraicClosure K) p n).comp f) (X.rootFunctional_ker_le f n)).comp
      ((X.tateEvalLinear n).quotKerEquivOfSurjective
        (X.tateEval_surjective_unconditional n)).symm.toLinearMap

omit [IsDomain R] [IsPrincipalIdealRing R] in
/-- Finite descent evaluates the original functional on any actual Tate lift. -/
theorem rootFunctionalLevel_eval (n : ℕ) (x : X.tateSequences) :
    X.rootFunctionalLevel f n (X.tateEvalLinear n x) =
      tateRootEval (AlgebraicClosure K) p n (f x) := by
  simp only [rootFunctionalLevel, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearMap.quotKerEquivOfSurjective_symm_apply, Submodule.liftQ_apply]

/-- Finite Cartier duality realizes the descended character as an original dual point. -/
def rootFunctionalDualPoint (n : ℕ) : (X.cartierDual.level n).Points :=
  (X.level n).cartierCharactersEquiv.symm (Additive.ofMul
    (((tateRootValue (AlgebraicClosure K) p n).comp
      (X.rootFunctionalLevel f n).toAddMonoidHom).toMultiplicative))

/-- The recovered point has exactly the original finite-root values. -/
theorem rootFunctionalDualPoint_pairing (n : ℕ) (x : (X.level n).Points) :
    (X.level n).cartierPairing (X.rootFunctionalDualPoint f n) x =
      (tateRootValue (AlgebraicClosure K) p n (X.rootFunctionalLevel f n x)).toMul := by
  rw [← FF.cartierCharactersEquiv_apply]
  change ((X.level n).cartierCharactersEquiv
    ((X.level n).cartierCharactersEquiv.symm _)).toMul _ = _
  rw [AddEquiv.apply_symm_apply]
  rfl

/-- A lifted original Tate vector evaluates the recovered dual point by the given functional. -/
theorem rootFunctionalDualPoint_eval (n : ℕ) (x : X.tateSequences) :
    (X.level n).cartierPairing (X.rootFunctionalDualPoint f n) (X.tateEval n x) =
      (tateRootValue (AlgebraicClosure K) p n
        (tateRootEval (AlgebraicClosure K) p n (f x))).toMul := by
  rw [X.rootFunctionalDualPoint_pairing]
  change (tateRootValue (AlgebraicClosure K) p n
    (X.rootFunctionalLevel f n (X.tateEvalLinear n x))).toMul = _
  rw [X.rootFunctionalLevel_eval]
end ThreeAdicPlan.PDivisibleSystem
