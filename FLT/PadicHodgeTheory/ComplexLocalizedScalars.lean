/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.PadicHodgeTheory.ComplexLocalizedFrobenius
public import FLT.PadicHodgeTheory.ComplexPadicScalarAction

/-! # P-adic scalars in the actual localization A_inf[1/p] -/

@[expose] public noncomputable section
namespace PadicHodgeTheory
variable (p : ℕ) [Fact p.Prime]

/-- Integral scalars in the localized Witt ring. -/
def complexPadicIntToLocalized : ℤ_[p] →+* ComplexAinfInvertP p :=
  (algebraMap (Ainf p) (ComplexAinfInvertP p)).comp (complexPadicIntToAinf p)

/-- Every nonzero integral p-adic scalar is invertible after inverting p. -/
theorem complexPadicIntToLocalized_isUnit (x : ℤ_[p]) (hx : x ≠ 0) :
    IsUnit (complexPadicIntToLocalized p x) := by
  obtain ⟨n, hn⟩ := IsDiscreteValuationRing.associated_pow_irreducible hx
    (PadicInt.irreducible_p (p := p))
  apply (hn.map (complexPadicIntToLocalized p)).isUnit_iff.mpr
  simpa only [map_pow, map_natCast] using
    (IsLocalization.Away.algebraMap_isUnit (S := ComplexAinfInvertP p) (p : Ainf p)).pow n

/-- The p-adic field embeds before the de Rham completion. -/
def complexPadicToLocalized : ℚ_[p] →+* ComplexAinfInvertP p :=
  IsLocalization.lift (M := nonZeroDivisors ℤ_[p]) (g := complexPadicIntToLocalized p)
    (fun x ↦ complexPadicIntToLocalized_isUnit p x (nonZeroDivisors.ne_zero x.property))

/-- Compatibility with the integral scalar map. -/
theorem complexPadicToLocalized_int (x : ℤ_[p]) :
    complexPadicToLocalized p (algebraMap ℤ_[p] ℚ_[p] x) = complexPadicIntToLocalized p x :=
  IsLocalization.lift_eq _ _

/-- These are the same scalars used by the family's de Rham construction. -/
theorem complexPadicToLocalized_deRham (x : ℚ_[p]) :
    algebraMap (ComplexAinfInvertP p) (ComplexBDeRhamPlus p)
      (complexPadicToLocalized p x) = complexPadicToDeRham p x := by
  suffices h : (algebraMap (ComplexAinfInvertP p) (ComplexBDeRhamPlus p)).comp
      (complexPadicToLocalized p) = complexPadicToDeRham p from DFunLike.congr_fun h x
  apply IsLocalization.ringHom_ext (nonZeroDivisors ℤ_[p])
  ext y
  simp only [RingHom.comp_apply, complexPadicToLocalized_int, complexPadicToDeRham_int]
  rfl

/-- Frobenius fixes the entire p-adic field, including denominators. -/
theorem complexPadicToLocalized_frobenius (x : ℚ_[p]) :
    complexLocalizedFrobenius p (complexPadicToLocalized p x) = complexPadicToLocalized p x := by
  suffices h : (complexLocalizedFrobenius p).comp (complexPadicToLocalized p) =
      complexPadicToLocalized p from DFunLike.congr_fun h x
  apply IsLocalization.ringHom_ext (nonZeroDivisors ℤ_[p])
  ext y
  simp only [RingHom.comp_apply, complexPadicToLocalized_int,
    complexPadicIntToLocalized, complexLocalizedFrobenius_algebraMap,
    complexAinfFrobenius_padic]

/-- Galois fixes the same p-adic scalars before completion. -/
theorem complexPadicToLocalized_galois (σ : PadicGalois p) (x : ℚ_[p]) :
    complexLocalizedGalois p σ (complexPadicToLocalized p x) = complexPadicToLocalized p x := by
  suffices h : (complexLocalizedGalois p σ).comp (complexPadicToLocalized p) =
      complexPadicToLocalized p from DFunLike.congr_fun h x
  apply IsLocalization.ringHom_ext (nonZeroDivisors ℤ_[p])
  ext y
  simp only [RingHom.comp_apply, complexPadicToLocalized_int,
    complexPadicIntToLocalized, complexLocalizedGalois_algebraMap,
    complexPadicIntToAinf_galois]

/-- Rational scalars for the divided-power construction, through the actual p-adic embedding. -/
scoped instance complexLocalizedRatAlgebra : Algebra ℚ (ComplexAinfInvertP p) :=
  ((complexPadicToLocalized p).comp (algebraMap ℚ ℚ_[p])).toAlgebra

end PadicHodgeTheory
