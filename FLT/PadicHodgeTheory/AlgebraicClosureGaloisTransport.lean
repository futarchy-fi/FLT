/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import Mathlib.FieldTheory.AbsoluteGaloisGroup

/-! # Galois conjugation along an isomorphism of base fields -/

@[expose] public noncomputable section
namespace PadicHodgeTheory
variable {K L : Type*} [Field K] [Field L] (e : K ≃+* L)

/-- Fix a closure isomorphism extending the specified original field isomorphism. -/
def closureFieldTransport : AlgebraicClosure K ≃+* AlgebraicClosure L :=
  IsAlgClosure.equivOfEquiv _ _ e

/-- The chosen closure transport extends the original field map. -/
theorem closureFieldTransport_algebraMap (x : K) :
    closureFieldTransport e (algebraMap K (AlgebraicClosure K) x) =
      algebraMap L (AlgebraicClosure L) (e x) :=
  IsAlgClosure.equivOfEquiv_algebraMap _ _ e x

/-- Its inverse extends the inverse of that same field map. -/
theorem closureFieldTransport_symm_algebraMap (x : L) :
    (closureFieldTransport e).symm (algebraMap L (AlgebraicClosure L) x) =
      algebraMap K (AlgebraicClosure K) (e.symm x) :=
  IsAlgClosure.equivOfEquiv_symm_algebraMap _ _ e x

/-- Conjugation transports the actual absolute Galois groups. -/
def closureGaloisTransport : Gal(AlgebraicClosure K/K) ≃* Gal(AlgebraicClosure L/L) where
  toFun σ :=
    { (closureFieldTransport e).symm.trans (σ.toRingEquiv.trans (closureFieldTransport e)) with
      commutes' x := by
        change closureFieldTransport e (σ ((closureFieldTransport e).symm
          (algebraMap L (AlgebraicClosure L) x))) = _
        rw [closureFieldTransport_symm_algebraMap, σ.commutes,
          closureFieldTransport_algebraMap, e.apply_symm_apply] }
  invFun τ :=
    { (closureFieldTransport e).trans (τ.toRingEquiv.trans (closureFieldTransport e).symm) with
      commutes' x := by
        change (closureFieldTransport e).symm (τ (closureFieldTransport e
          (algebraMap K (AlgebraicClosure K) x))) = _
        rw [closureFieldTransport_algebraMap, τ.commutes,
          closureFieldTransport_symm_algebraMap, e.symm_apply_apply] }
  left_inv σ := by ext x; simp
  right_inv τ := by ext x; simp
  map_mul' σ τ := by ext x; simp

/-- The chosen closure map intertwines the original actions, on every original vector. -/
theorem closureGaloisTransport_apply (σ : Gal(AlgebraicClosure K/K))
    (x : AlgebraicClosure K) :
    closureGaloisTransport e σ (closureFieldTransport e x) = closureFieldTransport e (σ x) := by
  change closureFieldTransport e (σ ((closureFieldTransport e).symm
    (closureFieldTransport e x))) = _
  rw [RingEquiv.symm_apply_apply]

end PadicHodgeTheory
