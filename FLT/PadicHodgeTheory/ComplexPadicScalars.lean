/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.PadicHodgeTheory.ComplexCyclotomicCompleted
public import Mathlib.RingTheory.WittVector.Compare

/-! # Actual p-adic scalar embeddings in the de Rham period ring -/

@[expose] public noncomputable section
namespace PadicHodgeTheory
variable (p : ℕ) [Fact p.Prime]

/-- Integral p-adic scalars enter A_inf through the Witt vectors of its prime field. -/
def complexPadicIntToAinf : ℤ_[p] →+* Ainf p :=
  (WittVector.map (ZMod.castHom (dvd_refl p) (IntegralTilt p))).comp
    (WittVector.equiv p).symm.toRingHom

/-- The actual integral scalar map into the completed de Rham ring. -/
def complexPadicIntToDeRham : ℤ_[p] →+* ComplexBDeRhamPlus p :=
  (complexAinfToDeRham p).comp (complexPadicIntToAinf p)

/-- Every nonzero integral p-adic scalar becomes a unit in the period ring. -/
theorem complexPadicIntToDeRham_isUnit (x : ℤ_[p]) (hx : x ≠ 0) :
    IsUnit (complexPadicIntToDeRham p x) := by
  obtain ⟨n, hn⟩ := IsDiscreteValuationRing.associated_pow_irreducible hx
    (PadicInt.irreducible_p (p := p))
  have h := hn.map (complexPadicIntToDeRham p)
  apply h.isUnit_iff.mpr
  simpa only [map_pow, map_natCast] using
    (complexDeRhamNat_isUnit p p (Fact.out : p.Prime).ne_zero).pow n

/-- Extend the scalar map by the fraction-ring universal property. -/
def complexPadicToDeRham : ℚ_[p] →+* ComplexBDeRhamPlus p :=
  IsLocalization.lift (M := nonZeroDivisors ℤ_[p]) (g := complexPadicIntToDeRham p)
    (fun x ↦ complexPadicIntToDeRham_isUnit p x (nonZeroDivisors.ne_zero x.property))

/-- The field scalar map agrees with the integral scalar map. -/
theorem complexPadicToDeRham_int (x : ℤ_[p]) :
    complexPadicToDeRham p (algebraMap ℤ_[p] ℚ_[p] x) = complexPadicIntToDeRham p x :=
  IsLocalization.lift_eq _ _

/-- These are embeddings into the actual ring, not formal coefficient parameters. -/
theorem complexPadicToDeRham_injective : Function.Injective (complexPadicToDeRham p) :=
  (complexPadicToDeRham p).injective

/-- The integral scalar map is injective as well. -/
theorem complexPadicIntToDeRham_injective : Function.Injective (complexPadicIntToDeRham p) := by
  intro x y h
  apply IsFractionRing.injective ℤ_[p] ℚ_[p]
  apply complexPadicToDeRham_injective p
  simpa only [complexPadicToDeRham_int] using h

end PadicHodgeTheory
