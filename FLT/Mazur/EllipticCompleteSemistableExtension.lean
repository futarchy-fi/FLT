/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticSemistableExtension
public import FLT.Mazur.FiniteDVRAbsoluteRamification
public import FLT.Mazur.FiniteDVRComplete

/-!
# Complete semistable extensions at large unramified primes

The constructed semistable extension is complete and Henselian, has finite
residue field of the same characteristic, and satisfies the absolute
ramification bound needed for finite-flat rigidity. No torsion closure or
specialization comparison is asserted here.
-/

@[expose] public section

namespace FLT.Mazur

open WeierstrassCurve IsLocalRing

universe u

variable {R K : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [IsAdicComplete (maximalIdeal R) R] [Finite (ResidueField R)]
  [Field K] [Algebra R K] [IsFractionRing R K]

/-- Complete semistable extension with an absolute small-ramification bound.
The hypothesis that p is irreducible expresses unramifiedness of the base. -/
theorem exists_complete_semistable_extension (p : ℕ) [CharP (ResidueField R) p]
    (hp : Irreducible (p : R)) (hp17 : 17 ≤ p) (W : WeierstrassCurve R) (hΔ : W.Δ ≠ 0) :
    ∃ (L : Type u) (_ : Field L) (_ : Algebra K L) (_ : FiniteDimensional K L)
      (_ : Algebra R L) (_ : IsScalarTower R K L) (S : Type u) (_ : CommRing S)
      (_ : IsDomain S) (_ : IsDiscreteValuationRing S) (_ : Algebra R S)
      (_ : Module.Finite R S) (_ : Algebra S L) (_ : IsScalarTower R S L)
      (_ : IsFractionRing S L) (_ : IsIntegralClosure S R L)
      (U : WeierstrassCurve S) (C : VariableChange L),
      IsAdicComplete (maximalIdeal S) S ∧ HenselianLocalRing S ∧
      CharP (ResidueField S) p ∧ Finite (ResidueField S) ∧
      Module.finrank K L ≤ 6 ∧ (maximalIdeal S).ramificationIdx R ≤ 6 ∧
      RaynaudParameters.order (p : S) < p - 1 ∧
      ((U.map (algebraMap S L)).HasGoodReduction S ∨
        (U.map (algebraMap S L)).HasMultiplicativeReduction S) ∧
      C • W.map (algebraMap R L) = U.map (algebraMap S L) := by
  obtain ⟨h2, h3⟩ := two_three_units_of_residue_char_gt_three (R := R) p (by omega)
  obtain ⟨L, hL, aK, fin, aR, towerK, S, hS, dom, dvr, aS, finS, aSL, towerS,
    frac, closure, U, C, hdeg, he, hred, hC⟩ :=
    exists_semistable_extension_of_two_three_units (K := K) W hΔ h2 h3
  have hinj : Function.Injective (algebraMap R L) := by
    rw [IsScalarTower.algebraMap_eq R K L]
    exact (algebraMap K L).injective.comp (IsFractionRing.injective R K)
  have : FaithfulSMul R S := (faithfulSMul_iff_algebraMap_injective R S).mpr (by
    intro x y hxy
    apply hinj
    rw [IsScalarTower.algebraMap_apply R S L, IsScalarTower.algebraMap_apply R S L, hxy])
  have hc : CharP (ResidueField S) p := charP_of_injective_algebraMap
    (algebraMap (ResidueField R) (ResidueField S)).injective p
  have hf : Finite (ResidueField S) :=
    IsLocalRing.ResidueField.finite_of_finite (R := R) (S := S) inferInstance
  exact ⟨L, hL, aK, fin, aR, towerK, S, hS, dom, dvr, aS, finS, aSL, towerS,
    frac, closure, U, C, finiteDVR_isAdicComplete (R := R),
    finiteDVR_henselian (R := R), hc, hf, hdeg, he,
    prime_order_lt_of_ramification_le_six p hp he hp17, hred, hC⟩

end FLT.Mazur
