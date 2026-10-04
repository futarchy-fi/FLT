/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.PadicHodgeTheory.ComplexDividedPowerHull

/-! # Galois action on the constructed embedded divided-power hull -/

@[expose] public noncomputable section
open scoped PadicHodgeTheory
namespace PadicHodgeTheory
variable (p : ℕ) [Fact p.Prime]

/-- The ambient action preserves rational divided powers of theta-kernel elements. -/
theorem complexLocalizedGalois_dpow (σ : PadicGalois p) (n : ℕ)
    {x : ComplexAinfInvertP p} (hx : x ∈ ComplexDeRhamIdeal p) :
    complexLocalizedGalois p σ ((complexLocalizedThetaDividedPowers p).dpow n x) =
      (complexLocalizedThetaDividedPowers p).dpow n (complexLocalizedGalois p σ x) := by
  apply (IsUnit.natCast_factorial_of_algebra ℚ n).mul_left_cancel
  calc
    (n.factorial : ComplexAinfInvertP p) * complexLocalizedGalois p σ
        ((complexLocalizedThetaDividedPowers p).dpow n x) =
      complexLocalizedGalois p σ
        ((n.factorial : ComplexAinfInvertP p) *
          (complexLocalizedThetaDividedPowers p).dpow n x) := by
            rw [map_mul, map_natCast]
    _ = complexLocalizedGalois p σ x ^ n := by
      rw [(complexLocalizedThetaDividedPowers p).factorial_mul_dpow_eq_pow hx, map_pow]
    _ = _ := ((complexLocalizedThetaDividedPowers p).factorial_mul_dpow_eq_pow
      (complexLocalizedGalois_ideal p σ hx)).symm

/-- The actual Galois action preserves the constructed hull. -/
theorem complexLocalizedGalois_mem_pdHull (σ : PadicGalois p) :
    complexAinfPDHullSubring p ≤
      (complexAinfPDHullSubring p).comap (complexLocalizedGalois p σ) := by
  apply (complexLocalizedThetaDividedPowers p).map_mem_hull
  · rintro x ⟨a, rfl⟩
    exact ⟨complexAinfGalois p σ a, (complexLocalizedGalois_algebraMap p σ a).symm⟩
  · exact fun n _ hx ↦ complexLocalizedGalois_dpow p σ n hx

/-- Restrict Galois to the embedded integral divided-power hull. -/
def complexPDHullGalois (σ : PadicGalois p) : ComplexAinfPDHull p →+* ComplexAinfPDHull p :=
  ((complexLocalizedGalois p σ).comp (complexAinfPDHullSubring p).subtype).codRestrict _
    (fun x ↦ complexLocalizedGalois_mem_pdHull p σ x.property)

/-- The identity acts as the identity on the hull. -/
@[simp] theorem complexPDHullGalois_one : complexPDHullGalois p 1 = RingHom.id _ := by
  apply RingHom.ext
  intro x
  apply Subtype.ext
  exact DFunLike.congr_fun (complexLocalizedGalois_one p) (x : ComplexAinfInvertP p)

/-- Composition agrees with multiplication in the original absolute Galois group. -/
theorem complexPDHullGalois_mul (σ τ : PadicGalois p) :
    complexPDHullGalois p (σ * τ) =
      (complexPDHullGalois p σ).comp (complexPDHullGalois p τ) := by
  apply RingHom.ext
  intro x
  apply Subtype.ext
  exact DFunLike.congr_fun (complexLocalizedGalois_mul p σ τ) (x : ComplexAinfInvertP p)

/-- The map to the family's de Rham ring intertwines the actual Galois actions. -/
theorem complexPDHullToDeRham_galois (σ : PadicGalois p) (x : ComplexAinfPDHull p) :
    complexPDHullToDeRham p (complexPDHullGalois p σ x) =
      complexDeRhamGalois p σ (complexPDHullToDeRham p x) :=
  (complexDeRhamGalois_algebraMap p σ x).symm

end PadicHodgeTheory
