/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.RingTheory.Jacobson.Ring
public import Mathlib.FieldTheory.IsAlgClosed.Basic

/-!
# Original rational points avoiding a nonnilpotent function

Over an algebraically closed field, a nonnilpotent function on a finite-type
affine algebra admits an original rational point where it does not vanish.
This supplies actual points for coefficient conditions obtained from an
arbitrary larger coefficient field.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.AffineRationalNonvanishing
variable {k A : Type*} [Field k] [IsAlgClosed k] [CommRing A]
  [Algebra k A] [Algebra.FiniteType k A]

/-- A nonnilpotent function survives at an actual rational point. -/
theorem exists_point (a : A) (ha : ¬ IsNilpotent a) :
    ∃ p : A →ₐ[k] k, p a ≠ 0 := by
  let _ : IsJacobsonRing A := isJacobsonRing_of_finiteType (A := k)
  have hn : a ∉ (⊥ : Ideal A).jacobson := by
    rw [← Ideal.radical_eq_jacobson]
    exact ha
  obtain ⟨m, hm, ham⟩ : ∃ m : Ideal A, m.IsMaximal ∧ a ∉ m := by
    by_contra! h
    exact hn (Ideal.mem_sInf.mpr fun m hm ↦ h m hm.2)
  let _ := hm
  let _ : Field (A ⧸ m) := Ideal.Quotient.field m
  let _ : Module.Finite k (A ⧸ m) := finite_of_finite_type_of_isJacobsonRing k (A ⧸ m)
  let q : (A ⧸ m) →ₐ[k] k := IsAlgClosed.lift
  refine ⟨q.comp (Ideal.Quotient.mkₐ k m), fun h ↦ ham ?_⟩
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  exact q.injective (h.trans (map_zero q).symm)

/-- On a reduced affine algebra every nonzero coefficient has a detecting rational point. -/
theorem exists_point_of_ne_zero [IsReduced A] (a : A) (ha : a ≠ 0) :
    ∃ p : A →ₐ[k] k, p a ≠ 0 :=
  exists_point a (by simpa only [isNilpotent_iff_eq_zero] using ha)

end FLT.Mazur.AffineRationalNonvanishing
