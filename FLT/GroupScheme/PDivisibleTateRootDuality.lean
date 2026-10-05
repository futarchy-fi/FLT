/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.PDivisibleRootFunctionalDescent

/-! # Perfect integral Tate Cartier duality with the actual coherent-root module -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace ThreeAdicPlan.PDivisibleSystem
variable {R K : Type} [CommRing R] [IsLocalRing R] [Field K] [Algebra R K]
  [IsDomain R] [IsPrincipalIdealRing R] [IsFractionRing R K] [CharZero K]
  {p height : ℕ} [Fact p.Prime] (X : PDivisibleSystem R K p height)
  (f : X.tateSequences →ₗ[ℤ_[p]] TateRootModule (AlgebraicClosure K) p)

/-- Finite Cartier representatives are coherent under the actual transposed inclusions. -/
theorem rootFunctionalDualPoint_transition {m n : ℕ} (h : m ≤ n) :
    genericHom (X.inclusion h).cartierDual (X.rootFunctionalDualPoint f n) =
      X.rootFunctionalDualPoint f m := by
  apply (X.level m).cartierPairing_separates_dual
  intro a
  obtain ⟨x, rfl⟩ := X.tateEval_surjective_unconditional m a
  rw [ModelHom.cartierPairing_naturality, ← X.tateEval_reduction h x,
    ← genericHom_comp, X.reduction_inclusion, FF.genericHom_multiply,
    FF.cartierPairing_nsmul_right, X.rootFunctionalDualPoint_eval,
    X.tateEval_reduction, X.rootFunctionalDualPoint_eval]
  exact congrArg (fun z : TateRootLevel (AlgebraicClosure K) p m ↦ z.toMul.val)
    ((f x).property h)

/-- Every actual root-valued functional gives a coherent vector on the original dual levels. -/
def rootFunctionalTate : X.CartierTate :=
  ⟨fun n ↦ X.rootFunctionalDualPoint f n, fun h ↦ X.rootFunctionalDualPoint_transition f h⟩

/-- The reconstructed dual vector recovers the whole original root-valued functional. -/
theorem tateRootPairing_rootFunctionalTate : X.tateRootPairing (X.rootFunctionalTate f) = f := by
  apply LinearMap.ext
  intro x
  apply tateRoot_ext
  intro n
  apply Additive.toMul.injective
  exact X.rootFunctionalDualPoint_eval f n x

/-- Perfectness is surjectivity onto all p-adic linear functionals with genuine root values. -/
theorem tateRootPairing_surjective : Function.Surjective X.tateRootPairing :=
  fun f ↦ ⟨X.rootFunctionalTate f, X.tateRootPairing_rootFunctionalTate f⟩

/-- Perfect integral Cartier duality on the two original Tate modules. -/
def tateRootDuality : X.CartierTate ≃ₗ[ℤ_[p]]
    (X.tateSequences →ₗ[ℤ_[p]] TateRootModule (AlgebraicClosure K) p) :=
  LinearEquiv.ofBijective X.tateRootPairing
    ⟨X.tateRootPairing_injective, X.tateRootPairing_surjective⟩

/-- The perfect comparison is the actual Cartier pairing at every original finite level. -/
theorem tateRootDuality_value (y : X.CartierTate) (x : X.tateSequences) (n : ℕ) :
    tateRootValue (AlgebraicClosure K) p n
      (tateRootEval (AlgebraicClosure K) p n (X.tateRootDuality y x)) =
        Additive.ofMul (X.cartierTatePairing y x n) := rfl
end ThreeAdicPlan.PDivisibleSystem
