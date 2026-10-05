/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.PDivisiblePointColimitGroup
public import FLT.GroupScheme.RationalPlacePointPrecision

/-! # The original completed point group over O_C

The coordinates range over all positive p-power precisions, a cofinal subsystem
of the residue tower. The finite-level index is colimited inside each coordinate;
it is not bounded uniformly along a completed point.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open PadicHodgeTheory
namespace ThreeAdicPlan.PDivisibleSystem
variable {p height : ℕ} [Fact p.Prime]
  (X : PDivisibleSystem ((LocalCyclotomic.rationalPlace p).adicCompletionIntegers ℚ)
    ((LocalCyclotomic.rationalPlace p).adicCompletion ℚ) p height)

/-- Compatible original colimit points, with the coordinatewise convolution law. -/
def rationalPlaceCompletedPointSubgroup :
    Subgroup (∀ s : ℕ, X.PointColimit (ComplexIntegerModPow p (s + 1))) where
  carrier := {x | ∀ s, X.pointColimitMap
    (rationalPlaceIntegerModPowReduce p (Nat.le_succ (s + 1))) (x (s + 1)) = x s}
  one_mem' _s := X.pointColimitMap_one _
  mul_mem' {x y} hx hy s :=
    (X.pointColimitMap_mul (rationalPlaceIntegerModPowReduce p (Nat.le_succ (s + 1)))
      (x (s + 1)) (y (s + 1))).trans (congrArg₂ (· * ·) (hx s) (hy s))
  inv_mem' {x} hx s :=
    (map_inv (X.pointColimitMapHom
      (rationalPlaceIntegerModPowReduce p (Nat.le_succ (s + 1)))) (x (s + 1))).trans
      (congrArg Inv.inv (hx s))

/-- The completed points of the original system, not its Tate module or universal cover. -/
abbrev RationalPlaceCompletedPoints := X.rationalPlaceCompletedPointSubgroup

/-- Evaluation at positive precision s+1 is a group homomorphism. -/
def rationalPlaceCompletedPointEval (s : ℕ) :
    X.RationalPlaceCompletedPoints →* X.PointColimit (ComplexIntegerModPow p (s + 1)) where
  toFun x := x.val s
  map_one' := rfl
  map_mul' _ _ := rfl

/-- Equality is detected at every original coefficient precision. -/
@[ext] theorem rationalPlaceCompletedPoints_ext (x y : X.RationalPlaceCompletedPoints)
    (h : ∀ s, X.rationalPlaceCompletedPointEval s x = X.rationalPlaceCompletedPointEval s y) :
    x = y := Subtype.ext (funext h)

/-- Adjacent compatibility implies compatibility across every precision gap. -/
theorem rationalPlaceCompletedPointEval_reduce (x : X.RationalPlaceCompletedPoints)
    {s t : ℕ} (h : s ≤ t) :
    X.pointColimitMap (rationalPlaceIntegerModPowReduce p (Nat.add_le_add_right h 1))
      (X.rationalPlaceCompletedPointEval t x) = X.rationalPlaceCompletedPointEval s x := by
  induction t, h using Nat.le_induction with
  | base => rw [rationalPlaceIntegerModPowReduce_refl, X.pointColimitMap_id]
  | succ t h ih =>
    rw [← rationalPlaceIntegerModPowReduce_comp (Nat.add_le_add_right h 1)
      (Nat.le_succ (t + 1)), X.pointColimitMap_comp]
    exact (congrArg (X.pointColimitMap _) (x.property t)).trans ih

/-- Every original O_C-valued colimit point has its compatible residue sequence. -/
def rationalPlacePointCompletion : X.PointColimit 𝓞_ℂ_[p] →* X.RationalPlaceCompletedPoints where
  toFun x := ⟨fun s ↦ X.pointColimitMap (Ideal.Quotient.mkₐ _ _) x, fun _ ↦ by
    rw [← X.pointColimitMap_comp]
    rfl⟩
  map_one' := by
    apply Subtype.ext
    funext s
    exact X.pointColimitMap_one
      (Ideal.Quotient.mkₐ _ (Ideal.span {(p : 𝓞_ℂ_[p]) ^ (s + 1)}))
  map_mul' x y := by
    apply Subtype.ext
    funext s
    exact X.pointColimitMap_mul
      (Ideal.Quotient.mkₐ _ (Ideal.span {(p : 𝓞_ℂ_[p]) ^ (s + 1)})) x y

/-- Finite-level specialization keeps the original coordinate map at every precision. -/
theorem rationalPlacePointCompletion_mk (n s : ℕ)
    (x : (X.level n).CoordinateRing →ₐ[(LocalCyclotomic.rationalPlace p).adicCompletionIntegers ℚ]
      𝓞_ℂ_[p]) :
    X.rationalPlaceCompletedPointEval s (X.rationalPlacePointCompletion (X.pointColimitMk n x)) =
      X.pointColimitMk n ((Ideal.Quotient.mkₐ _ _).comp x) := rfl

/-- Multiplication of original points specializes to powers in the completed group. -/
theorem rationalPlacePointCompletion_mul (N : ℕ) (x : X.PointColimit 𝓞_ℂ_[p]) :
    X.rationalPlacePointCompletion (X.pointColimitMul N x) =
      X.rationalPlacePointCompletion x ^ N := by
  rw [X.pointColimitMul_eq_pow, map_pow]

end ThreeAdicPlan.PDivisibleSystem
