/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonSmoothingReciprocalScaling
public import FLT.Mazur.AdicCompletionAlgEquiv

/-!
# Reciprocal scaling on every full node neighborhood

The original coordinate-ideal powers are invariant. Their quotient automorphisms
commute with every truncation and obey the unit action laws before passing to a limit.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.PolygonSmoothing
set_option backward.isDefEq.respectTransparency false
variable {R : Type*} [CommRing R] (t : R)

/-- Every full power of the actual node ideal is invariant. -/
theorem reciprocalScale_coordinateIdeal_pow (a : Rˣ) (m : ℕ) :
    (coordinateIdeal t ^ m).map (reciprocalScale t a).toRingHom = coordinateIdeal t ^ m := by
  rw [Ideal.map_pow, reciprocalScale_coordinateIdeal]

/-- Scaling on the mth full original node neighborhood. -/
def nodeScale (a : Rˣ) (m : ℕ) :
    (ChartRing t ⧸ coordinateIdeal t ^ m) ≃ₐ[R]
      (ChartRing t ⧸ coordinateIdeal t ^ m) :=
  Ideal.quotientEquivAlg _ _ (reciprocalScaleEquiv t a)
    (reciprocalScale_coordinateIdeal_pow t a m).symm

/-- The quotient automorphism is induced by scaling the original ring representatives. -/
@[simp] theorem nodeScale_mk (a : Rˣ) (m : ℕ) (x : ChartRing t) :
    nodeScale t a m (Ideal.Quotient.mk _ x) =
      Ideal.Quotient.mk _ (reciprocalScale t a x) :=
  Ideal.quotientEquivAlg_mk ..

/-- Scaling preserves the first original coordinate in each thickening with weight one. -/
theorem nodeScale_left (a : Rˣ) (m : ℕ) :
    nodeScale t a m (Ideal.Quotient.mk (coordinateIdeal t ^ m) (leftCoordinate t)) =
      Ideal.Quotient.mk (coordinateIdeal t ^ m)
        (algebraMap R (ChartRing t) a) * Ideal.Quotient.mk _ (leftCoordinate t) := by
  rw [nodeScale_mk, reciprocalScale_left, map_mul]

/-- Scaling preserves the second original coordinate with reciprocal weight. -/
theorem nodeScale_right (a : Rˣ) (m : ℕ) :
    nodeScale t a m (Ideal.Quotient.mk (coordinateIdeal t ^ m) (rightCoordinate t)) =
      Ideal.Quotient.mk (coordinateIdeal t ^ m)
        (algebraMap R (ChartRing t) ↑a⁻¹) * Ideal.Quotient.mk _ (rightCoordinate t) := by
  rw [nodeScale_mk, reciprocalScale_right, map_mul]

/-- The unit acts identically on the complete nonreduced neighborhood. -/
@[simp] theorem nodeScale_one (m : ℕ) :
    nodeScale t 1 m = AlgEquiv.refl := by
  ext x
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  simp

/-- The finite-neighborhood maps obey multiplication of units. -/
theorem nodeScale_mul (a b : Rˣ) (m : ℕ) (x : ChartRing t ⧸ coordinateIdeal t ^ m) :
    nodeScale t (a * b) m x = nodeScale t a m (nodeScale t b m x) := by
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  simp only [nodeScale_mk, reciprocalScale_mul, AlgHom.comp_apply]

/-- Scaling commutes with every original truncation map. -/
theorem nodeScale_transition (a : Rˣ) {m k : ℕ} (hmk : m ≤ k)
    (x : ChartRing t ⧸ coordinateIdeal t ^ k) :
    Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right hmk) (nodeScale t a k x) =
      nodeScale t a m (Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right hmk) x) := by
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  simp only [nodeScale_mk, Ideal.Quotient.factorₐ_apply_mk]

/-- The inverse uses exactly the inverse coefficient unit. -/
theorem nodeScale_inv (a : Rˣ) (m : ℕ) : (nodeScale t a m).symm = nodeScale t a⁻¹ m := by
  ext x
  apply (nodeScale t a m).injective
  rw [AlgEquiv.apply_symm_apply, ← nodeScale_mul, mul_inv_cancel, nodeScale_one]
  rfl

end FLT.Mazur.PolygonSmoothing
