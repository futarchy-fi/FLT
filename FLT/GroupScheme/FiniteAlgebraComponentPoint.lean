/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.FiniteAlgebraPointComponent
public import FLT.GroupScheme.GeometricFibrePoint

/-! # Every local factor over an algebraically closed field is a pointed component -/

@[expose] public noncomputable section

namespace FiniteAlgebra

variable {k A : Type*} [Field k] [CommRing A] [IsArtinianRing A] [Algebra k A]

/-- A point on a given factor selects that same factor in the original algebra. -/
theorem pointComponentIndex_eq_of_factor (m : ComponentIndex A) (β : Component A m →ₐ[k] k) :
    pointComponentIndex (β.comp (Ideal.Quotient.mkₐ k _)) = m := by
  let q : A →ₐ[k] Component A m := Ideal.Quotient.mkₐ k _
  have he : q (componentIdempotent A m) = 1 := by
    have hz : q (1 - componentIdempotent A m) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))
    rw [map_sub, map_one] at hz
    exact (sub_eq_zero.mp hz).symm
  apply ((existsUnique_pointComponent (β.comp q)).choose_spec.2 m ?_).symm
  change β (q (componentIdempotent A m)) = 1
  rw [he, map_one]

/-- Every finite local factor has a rational point over the geometric field. -/
theorem exists_pointComponentIndex_eq [IsAlgClosed k] [Module.Finite k A]
    (m : ComponentIndex A) : ∃ χ : A →ₐ[k] k, pointComponentIndex χ = m := by
  obtain ⟨β⟩ := Algebra.nonempty_hom_of_finite_of_isAlgClosed (Ω := k) (D := Component A m)
  exact ⟨β.comp (Ideal.Quotient.mkₐ k _), pointComponentIndex_eq_of_factor m β⟩

end FiniteAlgebra
