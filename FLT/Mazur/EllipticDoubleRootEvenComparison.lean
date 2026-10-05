/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticDoubleRootEvenCoordinates
public import FLT.Mazur.EllipticDoubleRootEvenSlope

/-!
# Actual component comparison in an even double-root chart

Equal simple residual x-labels give equal component classes. Each such
class is killed by two, as follows by applying the slope argument to a
point and itself.
-/

@[expose] public section

namespace FLT.Mazur

open WeierstrassCurve IsLocalRing

variable {K : Type*} [Field K] {A : ValuationSubring K} {W : WeierstrassCurve A}
  {π : A} {k : ℕ} {P Q : (W.map (algebraMap A K)).toProjective.Point}

/-- Two even-chart points over the same simple root have smooth sum. -/
theorem DoubleRootEvenCoordinates.smooth_add_of_same
    (v : DoubleRootEvenCoordinates A W π k P) (w : DoubleRootEvenCoordinates A W π k Q)
    (hπ : π ≠ 0) (hπm : π ∈ maximalIdeal A) (e1 e2 e3 e4 : A)
    (h1 : W.a₁ = π * e1) (h2 : W.a₂ = π * e2)
    (h3 : W.a₃ = π ^ (k + 3) * e3) (h4 : W.a₄ = π ^ (k + 3) * e4)
    (h6 : W.a₆ ∈ maximalIdeal A) (hx : residue A v.x = residue A w.x)
    (hd : 2 * residue A e2 * residue A v.x + residue A e4 ≠ 0) :
    SmoothReduction A W (P + Q) := by
  classical
  have hs := smoothReduction_add_of_doubleRoot_even_same A W hπ hπm k
    v.x v.y w.x w.y e1 e2 e3 e4 h1 h2 h3 h4 h6 v.nonsingular w.nonsingular hx hd
  rw [toProjective_add] at hs
  simpa only [v.represents, w.represents] using hs

/-- Equal simple residual x-labels give equal actual component classes. -/
theorem DoubleRootEvenCoordinates.component_eq_of_same
    (v : DoubleRootEvenCoordinates A W π k P) (w : DoubleRootEvenCoordinates A W π k Q)
    (hπ : π ≠ 0) (hπm : π ∈ maximalIdeal A) (e1 e2 e3 e4 : A)
    (h1 : W.a₁ = π * e1) (h2 : W.a₂ = π * e2)
    (h3 : W.a₃ = π ^ (k + 3) * e3) (h4 : W.a₄ = π ^ (k + 3) * e4)
    (h6 : W.a₆ ∈ maximalIdeal A) (hx : residue A v.x = residue A w.x)
    (hd : 2 * residue A e2 * residue A v.x + residue A e4 ≠ 0) :
    ellipticComponentHom A W P = ellipticComponentHom A W Q := by
  have hs : ellipticComponentHom A W P + ellipticComponentHom A W Q = 0 := by
    rw [← map_add, ellipticComponentHom_eq_zero]
    exact v.smooth_add_of_same w hπ hπm e1 e2 e3 e4 h1 h2 h3 h4 h6 hx hd
  have ht : ellipticComponentHom A W P + ellipticComponentHom A W P = 0 := by
    rw [← map_add, ellipticComponentHom_eq_zero]
    exact v.smooth_add_of_same v hπ hπm e1 e2 e3 e4 h1 h2 h3 h4 h6 rfl hd
  exact (add_left_cancel (hs.trans ht.symm)).symm

end FLT.Mazur
