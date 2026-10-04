/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.RaynaudCartierDual
public import FLT.GroupScheme.RaynaudModelArithmetic
public import FLT.GroupScheme.CartierDualConvolution

/-! # Arithmetic and rank of the actual integral Cartier dual -/

@[expose] public noncomputable section
namespace ThreeAdicPlan
variable {R K : Type} [CommRing R] [Field K] [Algebra R K]
  [IsDomain R] [IsPrincipalIdealRing R] [IsFractionRing R K] [CharZero K]

/-- Integral duality reverses composition on the actual local models. -/
@[simp] theorem ModelHom.cartierDual_comp {X Y Z : FF R K}
    (f : ModelHom X Y) (g : ModelHom Y Z) :
    (ModelHom.cartierDual (X := X) (Y := Z) (f.comp g)) = g.cartierDual.comp f.cartierDual :=
  HopfAlgebra.CartierDual.bialgMap_comp g f

/-- Duality preserves the zero group morphism. -/
@[simp] theorem ModelHom.cartierDual_zero (X Y : FF R K) :
    (ModelHom.zero X Y).cartierDual = ModelHom.zero Y.cartierDual X.cartierDual :=
  HopfAlgebra.CartierDual.bialgMap_convOne

/-- Duality preserves multiplication by each natural number. -/
@[simp] theorem FF.cartierDual_multiply (X : FF R K) (n : ℕ) :
    (X.multiply n).cartierDual = X.cartierDual.multiply n := by
  have h := HopfAlgebra.CartierDual.bialgMap_convPow (BialgHom.id R X.CoordinateRing) n
  rw [HopfAlgebra.CartierDual.bialgMap_id] at h
  exact h

/-- Annihilation of the original generic points implies annihilation of the dual points. -/
theorem FF.cartierDual_killed (X : FF R K) (n : ℕ) (h : ∀ x : X.Points, n • x = 0) :
    ∀ x : X.cartierDual.Points, n • x = 0 := by
  apply (X.cartierDual.multiply_eq_zero_iff n).mp
  rw [← X.cartierDual_multiply]
  rw [(X.multiply_eq_zero_iff n).mpr h, ModelHom.cartierDual_zero]

/-- The actual dual coordinate algebra has the original integral rank. -/
theorem FF.cartierDual_rank (X : FF R K) :
    Module.finrank R X.cartierDual.CoordinateRing = Module.finrank R X.CoordinateRing := by
  change Module.finrank R (HopfAlgebra.CartierDual R X.CoordinateRing) = _
  rw [(HopfAlgebra.CartierDual.linearEquiv (R := R) (A := X.CoordinateRing)).finrank_eq]
  let b := Module.Free.chooseBasis R X.CoordinateRing
  exact (b.dualBasis.repr.trans b.repr.symm).finrank_eq

end ThreeAdicPlan
