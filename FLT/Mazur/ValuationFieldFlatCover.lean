/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import Mathlib.RingTheory.Valuation.LocalSubring
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
public import Mathlib.RingTheory.RingHom.FaithfullyFlat

/-!
# Faithfully flat valuation extensions inside a specified field

A valuation ring embedded in a field has a dominating valuation subring of that
field. The original coefficient map factors through a local, faithfully flat
map to this subring. This provides the integral cover needed for geometric descent.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.ValuationFieldFlatCover

variable {R L : Type} [CommRing R] [IsDomain R] [ValuationRing R]
  [Field L] [Algebra R L] [FaithfulSMul R L]

/-- The specified field contains a valuation subring faithfully flat over the original base. -/
theorem exists_valuation_cover :
    ∃ (A : ValuationSubring L) (f : R →+* A),
      A.subtype.comp f = algebraMap R L ∧ IsLocalHom f ∧ f.FaithfullyFlat := by
  obtain ⟨A, hA, hlocal⟩ := IsLocalRing.exists_factor_valuationRing (algebraMap R L)
  let f : R →+* A := (algebraMap R L).codRestrict A.toSubring hA
  let _ : Algebra R A := f.toAlgebra
  let _ : IsLocalHom (algebraMap R A) := hlocal
  have hf : Function.Injective f := by
    intro x y h
    apply FaithfulSMul.algebraMap_injective R L
    exact congrArg Subtype.val h
  let _ : Module.IsTorsionFree R A := by
    apply Module.IsTorsionFree.of_smul_eq_zero
    intro r a h
    change f r * a = 0 at h
    rcases mul_eq_zero.mp h with hr | ha
    · exact Or.inl (hf (hr.trans (map_zero f).symm))
    · exact Or.inr ha
  let _ : Module.Flat R A := Module.Flat.flat_iff_torsion_eq_bot_of_isBezout.mpr
    (Submodule.isTorsionFree_iff_torsion_eq_bot.mp inferInstance)
  let _ : Module.FaithfullyFlat R A := Module.FaithfullyFlat.of_flat_of_isLocalHom
  exact ⟨A, f, rfl, hlocal, RingHom.faithfullyFlat_algebraMap_iff.mpr inferInstance⟩

end FLT.Mazur.ValuationFieldFlatCover
