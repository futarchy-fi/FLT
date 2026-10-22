/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RelativeDoubleRankScalarKernels
public import FLT.Mazur.RelativeDoubleRankTransposition

/-!
# Exact scalar transport across transposed rank charts

Scalars fixed by the endpoint exchange have identical exact kernels on the
transposed full charts. Residual corrections transfer before taking radicals.
No finite generation or coefficient reduction enters this transport.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.RelativeOrderedTuples
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {S B : Scheme.{0}} (E : Over S) [Etale E.hom] [IsSeparated E.hom]
  (x y : B ⟶ S) (τ : B ⟶ B) (hx : τ ≫ x = y) (hy : τ ≫ y = x)
  {R : Type} [CommRing R] (σ : R →+* Γ(B, ⊤)) (hσ : τ.appTop.hom.comp σ = σ)
  (n m r s : ℕ)

include hx hy hσ

/-- Transposition carries an original scalar equation to the identical scalar equation. -/
theorem doubleRankTranspose_scalar (a : R) :
    (doubleRankTranspose E x y τ hx hy n m r s).appTop
        ((doubleRankMap E x y m n s r).appTop (σ a)) =
      (doubleRankMap E x y n m r s).appTop (σ a) := by
  change (doubleRankTranspose E x y τ hx hy n m r s ≫
    doubleRankMap E x y m n s r).appTop (σ a) = _
  rw [doubleRankTranspose_map]
  change (doubleRankMap E x y n m r s).appTop (τ.appTop (σ a)) = _
  rw [show τ.appTop (σ a) = σ a from DFunLike.congr_fun hσ a]

/-- The exact unreduced scalar kernels agree after exchanging ranks and orders. -/
theorem doubleRankScalarKernel_transpose :
    doubleRankScalarKernel E x y σ n m r s =
      doubleRankScalarKernel E x y σ m n s r := by
  ext a
  constructor
  · intro ha
    have h := congrArg (doubleRankTranspose E x y τ hx hy m n s r).appTop ha
    change (doubleRankTranspose E x y τ hx hy m n s r).appTop
      ((doubleRankMap E x y n m r s).appTop (σ a)) = _ at h
    rw [doubleRankTranspose_scalar E x y τ hx hy σ hσ, map_zero] at h
    exact h
  · intro ha
    have h := congrArg (doubleRankTranspose E x y τ hx hy n m r s).appTop ha
    change (doubleRankTranspose E x y τ hx hy n m r s).appTop
      ((doubleRankMap E x y m n s r).appTop (σ a)) = _ at h
    rw [doubleRankTranspose_scalar E x y τ hx hy σ hσ, map_zero] at h
    exact h

/-- A fixed residual scalar corrects either full chart exactly when it corrects the other. -/
theorem doubleRankTranspose_correction_iff (a b : R) :
    (doubleRankMap E x y n m r s).appTop (σ a) =
        (doubleRankMap E x y n m r s).appTop (σ b) ↔
      (doubleRankMap E x y m n s r).appTop (σ a) =
        (doubleRankMap E x y m n s r).appTop (σ b) := by
  constructor
  · intro h
    have he := congrArg (doubleRankTranspose E x y τ hx hy m n s r).appTop h
    simpa only [doubleRankTranspose_scalar E x y τ hx hy σ hσ] using he
  · intro h
    have he := congrArg (doubleRankTranspose E x y τ hx hy n m r s).appTop h
    simpa only [doubleRankTranspose_scalar E x y τ hx hy σ hσ] using he

/-- Residual sums agree exactly, keeping the unchanged residual ideal. -/
theorem doubleRankScalarKernel_sup_transpose (H : Ideal R) :
    doubleRankScalarKernel E x y σ n m r s ⊔ H =
      doubleRankScalarKernel E x y σ m n s r ⊔ H := by
  rw [doubleRankScalarKernel_transpose E x y τ hx hy σ hσ]

end FLT.Mazur.RelativeOrderedTuples
