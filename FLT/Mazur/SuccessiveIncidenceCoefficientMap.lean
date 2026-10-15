/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.SuccessiveIncidenceAlgebra

/-!
# Incidence coordinates under arbitrary coefficient restriction

The retained coordinates t and u commute with a ring homomorphism of the
original coefficients, including quotient maps between arithmetic orders.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.SuccessiveIncidence
variable {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (π : R)

/-- Restrict the original coefficients and retain both incidence coordinates. -/
def coefficientRingMap : Coordinate π →+* Coordinate (f π) := by
  letI := f.toAlgebra
  exact (evaluation π (t (f π)) (u (f π)) (by
    rw [incidence, IsScalarTower.algebraMap_apply R S]
    rfl)).toRingHom

/-- Coefficient restriction retains the first incidence coordinate. -/
@[simp] theorem coefficientRingMap_t : coefficientRingMap f π (t π) = t (f π) := by
  let _ := f.toAlgebra
  unfold coefficientRingMap
  exact evaluation_t ..

/-- Coefficient restriction retains the second incidence coordinate. -/
@[simp] theorem coefficientRingMap_u : coefficientRingMap f π (u π) = u (f π) := by
  let _ := f.toAlgebra
  unfold coefficientRingMap
  exact evaluation_u ..

/-- Constants follow the specified coefficient homomorphism. -/
@[simp] theorem coefficientRingMap_algebraMap (r : R) :
    coefficientRingMap f π (algebraMap R _ r) = algebraMap S _ (f r) := by
  let _ := f.toAlgebra
  change (evaluation π (t (f π)) (u (f π)) _).toRingHom (algebraMap R _ r) = _
  rw [AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, AlgHom.commutes,
    IsScalarTower.algebraMap_apply R S]
  rfl

/-- Extended arithmetic ideals map into the chosen target arithmetic ideal. -/
theorem coefficientRingMap_ideal (I : Ideal R) (J : Ideal S) (hf : I ≤ J.comap f) :
    I.map (algebraMap R (Coordinate π)) ≤
      (J.map (algebraMap S (Coordinate (f π)))).comap (coefficientRingMap f π) := by
  rw [Ideal.map_le_iff_le_comap]
  intro r hr
  change coefficientRingMap f π (algebraMap R _ r) ∈ J.map (algebraMap S _)
  rw [coefficientRingMap_algebraMap]
  exact Ideal.mem_map_of_mem _ (hf hr)

end FLT.Mazur.SuccessiveIncidence
