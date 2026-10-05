/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.PDivisibleCartierBidual

/-! # Bidual evaluation is an equivalence on the original Tate modules -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace ThreeAdicPlan.PDivisibleSystem
variable {R K : Type} [CommRing R] [IsLocalRing R] [Field K] [Algebra R K]
  [IsDomain R] [IsPrincipalIdealRing R] [IsFractionRing R K] [CharZero K]
  {p height : ℕ} [Fact p.Prime] (X : PDivisibleSystem R K p height)

/-- The specified bidual Tate map evaluates to the actual finite bidual map. -/
theorem cartierBidualTateMap_eval (x : X.tateSequences) (n : ℕ) :
    X.cartierDual.cartierDual.tateEval n (X.cartierBidualTateMap x) =
      genericHom (X.level n).toCartierBidual (X.tateEval n x) := rfl

/-- Finite bidual evaluation detects equality of the original Tate vectors. -/
theorem cartierBidualTateMap_injective : Function.Injective X.cartierBidualTateMap := by
  intro x y h
  apply X.tate_ext
  intro n
  apply (X.level n).genericHom_toCartierBidual_bijective.1
  exact congrArg (X.cartierDual.cartierDual.tateEval n) h

/-- Unique finite bidual preimages are coherent under the original reductions. -/
theorem cartierBidualTateMap_surjective : Function.Surjective X.cartierBidualTateMap := by
  intro y
  choose x hx using fun n ↦ (X.level n).genericHom_toCartierBidual_bijective.2
    (X.cartierDual.cartierDual.tateEval n y)
  have hc {m n : ℕ} (h : m ≤ n) : genericHom (X.reduction h) (x n) = x m := by
    apply (X.level m).genericHom_toCartierBidual_bijective.1
    have hn := congrArg (fun f ↦ genericHom f (x n))
      (X.cartierBidualSystemHom.reduction_naturality h)
    rw [genericHom_comp, genericHom_comp] at hn
    change genericHom (X.level m).toCartierBidual (genericHom (X.reduction h) (x n)) = _
    change genericHom (X.level m).toCartierBidual (genericHom (X.reduction h) (x n)) =
      genericHom (X.cartierDual.cartierDual.reduction h)
        (genericHom (X.level n).toCartierBidual (x n)) at hn
    rw [hn, hx n, X.cartierDual.cartierDual.tateEval_reduction h, hx m]
  refine ⟨⟨x, fun h ↦ hc h⟩, ?_⟩
  apply X.cartierDual.cartierDual.tate_ext
  exact hx

/-- The equivalence uses the specified integral bidual map, without a replacement pairing. -/
def cartierBidualTateEquiv : X.tateSequences ≃ₗ[ℤ_[p]] X.cartierDual.CartierTate :=
  LinearEquiv.ofBijective X.cartierBidualTateMap
    ⟨X.cartierBidualTateMap_injective, X.cartierBidualTateMap_surjective⟩

/-- Bidual equivalence retains the originally constructed Tate map. -/
theorem cartierBidualTateEquiv_apply (x : X.tateSequences) :
    X.cartierBidualTateEquiv x = X.cartierBidualTateMap x := rfl
end ThreeAdicPlan.PDivisibleSystem
