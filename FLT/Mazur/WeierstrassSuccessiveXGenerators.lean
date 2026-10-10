/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSuccessiveXAlgebra

/-!
# Generators of the actual successive equation algebra

All three retained generators determine the image of the equation algebra.
This permits comparison with the Rees fraction chart over the preceding cubic.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.WeierstrassSuccessiveX

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
  (W : WeierstrassCurve R) (s π b3 b4 b6 : R)

/-- Containing all three generator images suffices to contain the chart image. -/
theorem range_le_of_coordinates (f : Coordinate W s π b3 b4 b6 →ₐ[R] S)
    (C : Subalgebra R S) (h : ∀ i, f (coord W s π b3 b4 b6 i) ∈ C) : f.range ≤ C := by
  rintro z ⟨a, rfl⟩
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective a
  let g := f.comp (Ideal.Quotient.mkₐ R (relations W s π b3 b4 b6))
  change g p ∈ C
  induction p using MvPolynomial.induction_on with
  | C a =>
    rw [MvPolynomial.C_eq_algebraMap, AlgHom.commutes]
    exact C.algebraMap_mem a
  | add p q hp hq =>
    rw [map_add]
    exact C.add_mem hp hq
  | mul_X p i hp =>
    rw [map_mul]
    exact C.mul_mem hp (h i)

/-- The retained incidence, slope and horizontal coordinates generate the whole algebra. -/
theorem coordinates_adjoin :
    Algebra.adjoin R (Set.range (coord W s π b3 b4 b6)) = ⊤ := by
  have h := range_le_of_coordinates W s π b3 b4 b6 (AlgHom.id R _)
    (Algebra.adjoin R (Set.range (coord W s π b3 b4 b6)))
    (fun i => Algebra.subset_adjoin ⟨i, rfl⟩)
  exact top_unique (fun z _ => h ⟨z, rfl⟩)

end FLT.Mazur.WeierstrassSuccessiveX
