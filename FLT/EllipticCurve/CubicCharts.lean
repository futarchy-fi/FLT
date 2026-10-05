/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.EllipticCurve.InfinityChart
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.AlgebraicGeometry.Limits

/-! # The two Weierstrass charts and their overlap -/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial

namespace WeierstrassCurve.CubicCharts

universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

/-- False is Z=1; true is Y=1, the previously constructed infinity chart. -/
def equation (b : Bool) : MvPolynomial (Fin 2) R :=
  if b then InfinityChart.equation W else
    X 1 ^ 2 + C W.a₁ * X 0 * X 1 + C W.a₃ * X 1 -
      (X 0 ^ 3 + C W.a₂ * X 0 ^ 2 + C W.a₄ * X 0 + C W.a₆)

/-- The coordinate ring of the selected affine equation. -/
abbrev Ring (b : Bool) := MvPolynomial (Fin 2) R ⧸ Ideal.span {equation W b}

/-- The image of an affine coordinate in the quotient ring. -/
def coord (b : Bool) (i : Fin 2) : Ring W b := Ideal.Quotient.mk _ (X i)

/-- The chart intersection, obtained by inverting the second coordinate. -/
abbrev Overlap (b : Bool) := Localization.Away (coord W b 1)

/-- An affine coordinate viewed on the chart intersection. -/
def loc (b : Bool) (i : Fin 2) : Overlap W b :=
  algebraMap (Ring W b) (Overlap W b) (coord W b i)

/-- The inverse of the second coordinate on the intersection. -/
def inv (b : Bool) : Overlap W b :=
  IsLocalization.Away.invSelf (coord W b 1)

@[simp] theorem loc_mul_inv (b : Bool) : loc W b 1 * inv W b = 1 :=
  IsLocalization.Away.mul_invSelf (coord W b 1)

@[simp] theorem inv_mul_loc (b : Bool) : inv W b * loc W b 1 = 1 := by
  rw [mul_comm, loc_mul_inv]

/-- Interchanging the two homogeneous denominators transforms the equation
by their cubic ratio. -/
theorem transition_identity (b : Bool) (x y t : R) (ht : t * y = 1) :
    eval ![x * t, t] (equation W (!b)) =
      t ^ 3 * eval ![x, y] (equation W b) := by
  cases b
  · simp only [equation, Bool.not_false, Bool.false_eq_true, ↓reduceIte,
      InfinityChart.equation, map_sub, map_add, map_mul, map_pow,
      eval_X, eval_C, Matrix.cons_val_zero, Matrix.cons_val_one]
    linear_combination -(t + t ^ 2 * y + W.a₁ * x * t ^ 2 + W.a₃ * t ^ 2) * ht
  · simp only [equation, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
      InfinityChart.equation, map_sub, map_add, map_mul, map_pow,
      eval_X, eval_C, Matrix.cons_val_zero, Matrix.cons_val_one]
    linear_combination -(t ^ 2 + W.a₁ * x * t ^ 2 + W.a₃ * t +
      W.a₃ * t ^ 2 * y) * ht +
      (W.a₂ * x ^ 2 * t ^ 2 + W.a₄ * x * t * (t * y + 1) +
        W.a₆ * ((t * y) ^ 2 + t * y + 1)) * ht

theorem map_equation {S : Type*} [CommRing S] (f : R →+* S) (b : Bool) :
    MvPolynomial.map f (equation W b) = equation (W.map f) b := by
  cases b <;> simp [equation, InfinityChart.equation, WeierstrassCurve.map]

theorem aeval_loc_equation (b : Bool) :
    aeval (loc W b) (equation W b) = 0 := by
  have he : (aeval (loc W b) : MvPolynomial (Fin 2) R →ₐ[R] Overlap W b) =
      (IsScalarTower.toAlgHom R (Ring W b) (Overlap W b)).comp
        (Ideal.Quotient.mkₐ R (Ideal.span {equation W b})) := by
    ext i
    simp only [aeval_X]
    rfl
  rw [he]
  change algebraMap (Ring W b) (Overlap W b)
    (Ideal.Quotient.mk _ (equation W b)) = 0
  rw [Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp)), map_zero]

theorem transition_root (b : Bool) :
    aeval ![loc W b 0 * inv W b, inv W b] (equation W (!b)) = 0 := by
  have h := transition_identity (W.map (algebraMap R (Overlap W b))) b
    (loc W b 0) (loc W b 1) (inv W b) (inv_mul_loc W b)
  rw [← map_equation W, ← map_equation W] at h
  simp only [eval_map] at h
  change aeval ![loc W b 0 * inv W b, inv W b] (equation W (!b)) =
    inv W b ^ 3 * aeval ![loc W b 0, loc W b 1] (equation W b) at h
  have hv : ![loc W b 0, loc W b 1] = loc W b := by ext i; fin_cases i <;> rfl
  rw [hv, aeval_loc_equation, mul_zero] at h
  exact h

/-- The coordinate change before localizing its source. -/
def changeChart (b : Bool) : Ring W (!b) →ₐ[R] Overlap W b :=
  Ideal.Quotient.liftₐ (Ideal.span {equation W (!b)})
    (aeval ![loc W b 0 * inv W b, inv W b]) (by
      change Ideal.span {equation W (!b)} ≤ RingHom.ker
        (aeval ![loc W b 0 * inv W b, inv W b]).toRingHom
      rw [Ideal.span_le]
      intro p hp
      rcases Set.mem_singleton_iff.mp hp with rfl
      exact transition_root W b)

@[simp] theorem changeChart_coord (b : Bool) (i : Fin 2) :
    changeChart W b (coord W (!b) i) =
      (![loc W b 0 * inv W b, inv W b] : Fin 2 → Overlap W b) i := by
  change aeval _ (X i) = _
  simp

/-- The coordinate change extends to the overlap localization. -/
def transition (b : Bool) : Overlap W (!b) →ₐ[R] Overlap W b :=
  IsLocalization.Away.liftAlgHom (coord W (!b) 1) (f := changeChart W b) (by
    rw [changeChart_coord]
    change IsUnit (inv W b)
    exact isUnit_iff_exists_inv.mpr ⟨loc W b 1, inv_mul_loc W b⟩)

@[simp] theorem transition_loc (b : Bool) (i : Fin 2) :
    transition W b (loc W (!b) i) =
      (![loc W b 0 * inv W b, inv W b] : Fin 2 → Overlap W b) i := by
  simp [transition, loc, IsLocalization.Away.liftAlgHom_apply, changeChart_coord]

@[simp] theorem transition_inv (b : Bool) :
    transition W b (inv W (!b)) = loc W b 1 := by
  have h := congrArg (transition W b) (loc_mul_inv W (!b))
  simp only [map_mul, map_one, transition_loc, Matrix.cons_val_one, Matrix.cons_val_zero] at h
  calc
    transition W b (inv W (!b)) =
        (loc W b 1 * inv W b) * transition W b (inv W (!b)) := by
          rw [loc_mul_inv, one_mul]
    _ = loc W b 1 := by rw [mul_assoc, h, mul_one]

theorem transition_false_true :
    (transition W false).comp (transition W true) = AlgHom.id R (Overlap W false) := by
  have hloc₀ := transition_loc W false
  have hloc₁ := transition_loc W true
  have hinv₀ := transition_inv W false
  have hinv₁ := transition_inv W true
  dsimp only [Bool.not] at hloc₀ hloc₁ hinv₀ hinv₁
  apply IsLocalization.algHom_ext (L := Overlap W false) (Submonoid.powers (coord W false 1))
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  intro i
  change transition W false (transition W true (loc W false i)) = loc W false i
  refine (congrArg (transition W false) (hloc₁ i)).trans ?_
  fin_cases i
  · change transition W false (loc W true 0 * inv W true) = loc W false 0
    calc
      _ = transition W false (loc W true 0) * transition W false (inv W true) :=
        map_mul _ _ _
      _ = (loc W false 0 * inv W false) * loc W false 1 :=
        congrArg₂ (· * ·) (hloc₀ 0) hinv₀
      _ = loc W false 0 := by rw [mul_assoc, inv_mul_loc, mul_one]
  · exact hinv₀

theorem transition_true_false :
    (transition W true).comp (transition W false) = AlgHom.id R (Overlap W true) := by
  have hloc₀ := transition_loc W false
  have hloc₁ := transition_loc W true
  have hinv₀ := transition_inv W false
  have hinv₁ := transition_inv W true
  dsimp only [Bool.not] at hloc₀ hloc₁ hinv₀ hinv₁
  apply IsLocalization.algHom_ext (L := Overlap W true) (Submonoid.powers (coord W true 1))
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  intro i
  change transition W true (transition W false (loc W true i)) = loc W true i
  refine (congrArg (transition W true) (hloc₀ i)).trans ?_
  fin_cases i
  · change transition W true (loc W false 0 * inv W false) = loc W true 0
    calc
      _ = transition W true (loc W false 0) * transition W true (inv W false) :=
        map_mul _ _ _
      _ = (loc W true 0 * inv W true) * loc W true 1 :=
        congrArg₂ (· * ·) (hloc₁ 0) hinv₁
      _ = loc W true 0 := by rw [mul_assoc, inv_mul_loc, mul_one]
  · exact hinv₁

/-- The actual algebra isomorphism used to glue the charts. -/
def overlapEquiv : Overlap W false ≃ₐ[R] Overlap W true :=
  AlgEquiv.ofAlgHom (transition W true) (transition W false)
    (transition_true_false W) (transition_false_true W)

end WeierstrassCurve.CubicCharts
