/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.PolygonSmoothingNilpotentUnit

/-!
# Nilpotent shears with an explicit smoothing drift

A full chart function supplies the left multiplier. Its scalar part supplies
the smoothing drift; the right coordinate compensates by the quotient of
these two units. This construction works at every nilpotent parameter order.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.PolygonSmoothing
set_option backward.isDefEq.respectTransparency false
variable {R : Type*} [CommRing R] (t e : R) (he : IsNilpotent e)
local notation "A" => ChartRing t
local notation "E" => algebraMap R A e

/-- One plus a nilpotent multiple, with its full finite inverse. -/
def nilpotentMultiplier (p : R) : Rˣ :=
  (show IsNilpotent (e * p) from by
    obtain ⟨n, hn⟩ := he
    exact ⟨n, by rw [mul_pow, hn, zero_mul]⟩).isUnit_one_add.unit

/-- The multiplier has exactly the requested value. -/
@[simp] theorem nilpotentMultiplier_val (p : R) :
    (nilpotentMultiplier e he p : R) = 1 + e * p := IsUnit.unit_spec _

include he in
/-- The principal coefficient ideal is nilpotent at the same finite order. -/
theorem nilpotentPrincipalIdeal : IsNilpotent (Ideal.span {e}) := by
  obtain ⟨n, hn⟩ := he
  refine ⟨n, ?_⟩
  rw [Ideal.span_singleton_pow, hn, Ideal.span_singleton_eq_bot.mpr rfl]
  rfl

/-- The full node multiplier retains all terms of the chosen function. -/
def nilpotentChartMultiplier (p : A) : Aˣ :=
  nilpotentMultiplier E (he.map (algebraMap R A)) p

/-- The complete chart multiplier is linear in the original nilpotent scalar. -/
@[simp] theorem nilpotentChartMultiplier_val (p : A) :
    (nilpotentChartMultiplier t e he p : A) = 1 + E * p := nilpotentMultiplier_val ..

/-- The full multiplier is congruent to one over the original coefficient ideal. -/
theorem nilpotentChartMultiplier_sub_mem (p : A) :
    (nilpotentChartMultiplier t e he p : A) - 1 ∈
      (Ideal.span {e}).map (algebraMap R A) := by
  rw [nilpotentChartMultiplier_val, add_sub_cancel_left]
  exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _
    (Ideal.subset_span (Set.mem_singleton e)))

/-- An arbitrary nilpotent chart correction, allowing its scalar smoothing drift. -/
irreducible_def nilpotentShearEquiv (c : R) (p : A) :
    ChartRing ((1 + e * c) * t) ≃ₐ[R] A :=
  (changeParameterEquiv t ((1 + e * c) * t) 1 (nilpotentMultiplier e he c)
    (by simp only [Units.val_one, one_mul, nilpotentMultiplier_val])).trans
      (balancedUnitEquiv t (Ideal.span {e}) (nilpotentPrincipalIdeal e he)
        (nilpotentChartMultiplier t e he p) (nilpotentChartMultiplier_sub_mem t e he p))

/-- The left coordinate has precisely the full prescribed nilpotent correction. -/
theorem nilpotentShearEquiv_left (c : R) (p : A) :
    nilpotentShearEquiv t e he c p (leftCoordinate ((1 + e * c) * t)) =
      leftCoordinate t * (1 + E * p) := by
  rw [nilpotentShearEquiv_def, AlgEquiv.trans_apply]
  change (balancedUnitEquiv t _ _ _ _).toAlgHom
    (changeParameter t ((1 + e * c) * t) 1 (nilpotentMultiplier e he c)
      (by simp only [Units.val_one, one_mul, nilpotentMultiplier_val])
      (leftCoordinate ((1 + e * c) * t))) = _
  rw [changeParameter_left, Units.val_one, map_one, one_mul,
    balancedUnitEquiv_toAlgHom, balancedUnitMap_left, nilpotentChartMultiplier_val]

/-- The right coordinate keeps the exact compensating inverse, including higher terms. -/
theorem nilpotentShearEquiv_right (c : R) (p : A) :
    nilpotentShearEquiv t e he c p (rightCoordinate ((1 + e * c) * t)) =
      algebraMap R A (1 + e * c) *
        (rightCoordinate t * ↑(nilpotentChartMultiplier t e he p)⁻¹) := by
  rw [nilpotentShearEquiv_def, AlgEquiv.trans_apply]
  change (balancedUnitEquiv t _ _ _ _).toAlgHom
    (changeParameter t ((1 + e * c) * t) 1 (nilpotentMultiplier e he c)
      (by simp only [Units.val_one, one_mul, nilpotentMultiplier_val])
      (rightCoordinate ((1 + e * c) * t))) = _
  rw [changeParameter_right, balancedUnitEquiv_toAlgHom, map_mul, AlgHom.commutes,
    balancedUnitMap_right, nilpotentMultiplier_val]

end FLT.Mazur.PolygonSmoothing
