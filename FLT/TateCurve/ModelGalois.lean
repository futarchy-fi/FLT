/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.TateCurve.ModelTransport

/-!
# Galois-fixed changes of Weierstrass coordinates

A coordinate change over an extension commutes with a base-field automorphism
whenever its four coefficients are fixed by that automorphism.
-/

@[expose] public section

open scoped WeierstrassCurve.Affine

namespace WeierstrassCurve.Affine.Point

variable {K L : Type*} [Field K] [Field L] [Algebra K L] [DecidableEq L]

/-- A fixed coordinate change intertwines the Galois actions on two base-changed curves. -/
theorem map_equivVariableChange_of_fixed (V W : WeierstrassCurve K)
    [(V.baseChange L).IsElliptic] (C : VariableChange L)
    (hC : C • V.baseChange L = W.baseChange L) (σ : L ≃ₐ[K] L)
    (hσ : C.map σ.toAlgHom.toRingHom = C) (P : (W⁄L).Point) :
    map σ.toAlgHom (equivVariableChange (V.baseChange L) C (equivOfEq hC.symm P)) =
      equivVariableChange (V.baseChange L) C (equivOfEq hC.symm (map σ.toAlgHom P)) := by
  have hu : σ (C.u : L) = C.u := congrArg (fun D : VariableChange L ↦ (D.u : L)) hσ
  have hr : σ C.r = C.r := congrArg VariableChange.r hσ
  have hs : σ C.s = C.s := congrArg VariableChange.s hσ
  have ht : σ C.t = C.t := congrArg VariableChange.t hσ
  cases P with
  | zero => simp only [← zero_def, map_zero, AddEquiv.map_zero]
  | some x y h =>
    erw [equivOfEq_some, equivVariableChange_some, map_some, map_some,
      equivOfEq_some, equivVariableChange_some, some.injEq]
    constructor <;> simp [map_add, map_mul, map_pow, hu, hr, hs, ht]

/-- The inverse transport of a fixed coordinate change is Galois equivariant. -/
theorem map_modelEquiv_of_fixed (V W : WeierstrassCurve K)
    [(V.baseChange L).IsElliptic] (C : VariableChange L)
    (hC : C • V.baseChange L = W.baseChange L) (σ : L ≃ₐ[K] L)
    (hσ : C.map σ.toAlgHom.toRingHom = C) (P : (V⁄L).Point) :
    map σ.toAlgHom (equivOfEq hC ((equivVariableChange (V.baseChange L) C).symm P)) =
      equivOfEq hC ((equivVariableChange (V.baseChange L) C).symm (map σ.toAlgHom P)) := by
  let e := (equivOfEq hC.symm).trans (equivVariableChange (V.baseChange L) C)
  have he : ∀ Q, map σ.toAlgHom (e Q) = e (map σ.toAlgHom Q) :=
    map_equivVariableChange_of_fixed V W C hC σ hσ
  have hinv : ∀ {A B : WeierstrassCurve L} (h : A = B) (Q : A.toAffine.Point),
      equivOfEq h Q = (equivOfEq h.symm).symm Q := by
    intro A B h Q
    subst B
    rfl
  simp only [hinv]
  change map σ.toAlgHom (e.symm P) = e.symm (map σ.toAlgHom P)
  apply e.injective
  rw [← he, e.apply_symm_apply, e.apply_symm_apply]

end WeierstrassCurve.Affine.Point
