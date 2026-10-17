/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.PolygonSmoothingNilpotentShearPunctures
public import FLT.Mazur.LaurentNearIdentityAutomorphism

/-!
# Both full puncture automorphisms of a nilpotent node shear

The opposite puncture retains the compensating inverse and scalar drift.
Both substitutions have constructed inverses on the entire Laurent algebra.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
namespace FLT.Mazur.PolygonSmoothing
open LaurentPolynomial LaurentUnitPoints
set_option backward.isDefEq.respectTransparency false
variable {R : Type*} [CommRing R] (t e : R) (he : IsNilpotent e)
local notation "L" => R[T;T⁻¹]
local notation "J" => Ideal.map (algebraMap R (LaurentPolynomial R))
  (Ideal.span (Set.singleton e))
local notation "r" => AlgHom.comp (leftLaurentMap t) (branchSwapMap t)

/-- Inverting a unit congruent to one preserves that congruence over any ideal. -/
theorem unit_inv_sub_one_mem {A : Type*} [CommRing A] (I : Ideal A) (v : Aˣ)
    (hv : (v : A) - 1 ∈ I) : (↑v⁻¹ : A) - 1 ∈ I := by
  have h : (↑v⁻¹ : A) - 1 = -((↑v⁻¹ : A) * ((v : A) - 1)) := by
    rw [mul_sub, Units.inv_mul, mul_one, neg_sub]
  rw [h]
  exact I.neg_mem (I.mul_mem_left _ hv)

/-- The outgoing coordinate differs from T by an element of the nilpotent coefficient ideal. -/
theorem nilpotentShearLeftUnit_sub_mem (p : ChartRing t) :
    (nilpotentShearLeftUnit t e he p : L) - T 1 ∈ J := by
  have h : C e ∈ J := Ideal.mem_map_of_mem _ (Ideal.subset_span (Set.mem_singleton e))
  rw [nilpotentShearLeftUnit_val]
  convert (J).mul_mem_left (T 1) ((J).mul_mem_right (leftLaurentMap t p) h) using 1
  · ring

/-- The compensating inverse coordinate also reduces to T, with every tail retained. -/
theorem nilpotentShearRightUnit_sub_mem (c : R) (p : ChartRing t) :
    (nilpotentShearRightUnit t e he c p : L) - T 1 ∈ J := by
  let v := Units.map (r).toMonoidHom (nilpotentChartMultiplier t e he p)
  have h : C e ∈ J := Ideal.mem_map_of_mem _ (Ideal.subset_span (Set.mem_singleton e))
  have hv : (v : L) - 1 ∈ J := by
    change r (nilpotentChartMultiplier t e he p : ChartRing t) - 1 ∈ J
    rw [nilpotentChartMultiplier_val, map_add, map_one, map_mul, AlgHom.commutes]
    simpa only [add_sub_cancel_left, C_eq_algebraMap] using (J).mul_mem_right (r p) h
  have hi := unit_inv_sub_one_mem J v hv
  have hc : C (1 + e * c) - 1 ∈ J := by
    rw [map_add, map_one, map_mul, add_sub_cancel_left]
    exact (J).mul_mem_right (C c) h
  have hsum := (J).mul_mem_left (T 1)
    ((J).add_mem ((J).mul_mem_right (↑v⁻¹ : L) hc) hi)
  rw [nilpotentShearRightUnit_val]
  change C (1 + e * c) * (T 1 * (↑v⁻¹ : L)) - T 1 ∈ J
  convert hsum using 1
  · ring

/-- The full outgoing puncture substitution as an algebra equivalence. -/
def nilpotentShearLeftEquiv (p : ChartRing t) : L ≃ₐ[R] L :=
  LaurentNearIdentityAutomorphism.equiv (Ideal.span {e}) (nilpotentPrincipalIdeal e he)
    (nilpotentShearLeftUnit t e he p) (nilpotentShearLeftUnit_sub_mem t e he p)

/-- The full opposite substitution, including its exact inverse compensation. -/
def nilpotentShearRightEquiv (c : R) (p : ChartRing t) : L ≃ₐ[R] L :=
  LaurentNearIdentityAutomorphism.equiv (Ideal.span {e}) (nilpotentPrincipalIdeal e he)
    (nilpotentShearRightUnit t e he c p) (nilpotentShearRightUnit_sub_mem t e he c p)

/-- The left equivalence retains the original full puncture map. -/
theorem nilpotentShearLeftEquiv_toAlgHom (p : ChartRing t) :
    (nilpotentShearLeftEquiv t e he p).toAlgHom =
      evalUnit (nilpotentShearLeftUnit t e he p) := rfl

/-- The right equivalence retains the original full puncture map. -/
theorem nilpotentShearRightEquiv_toAlgHom (c : R) (p : ChartRing t) :
    (nilpotentShearRightEquiv t e he c p).toAlgHom =
      evalUnit (nilpotentShearRightUnit t e he c p) := rfl

end FLT.Mazur.PolygonSmoothing
