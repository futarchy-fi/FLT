/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticValuationRingEquation

/-!
# Multiplicative invariants in the realized valuation ring

The multiplicative branch of S2a gives an actual nodal equation in the
canonical valuation subring: its discriminant is in the maximal ideal and
its c₄ invariant is a unit. Its generic curve is the original elliptic curve.
-/

@[expose] public noncomputable section

namespace FLT.Mazur

open WeierstrassCurve IsLocalRing
open IsDedekindDomain.HeightOneSpectrum

variable {S L : Type*} [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
  [Field L] [Algebra S L] [IsFractionRing S L] (U : WeierstrassCurve S)

local notation "A" => fractionValuationSubring S L
local notation "V" => fractionValuationEquation (L := L) U

local instance : IsDiscreteValuationRing A := fractionValuationSubring_isDiscreteValuationRing S L

/-- The exact supplied multiplicative equation has the required nodal integral invariants. -/
theorem fractionValuationEquation_multiplicative_invariants
    [(U.map (algebraMap S L)).HasMultiplicativeReduction S] :
    (V).Δ ∈ maximalIdeal A ∧ IsUnit (V).c₄ := by
  have hd := HasMultiplicativeReduction.badReduction
    (R := S) (W := U.map (algebraMap S L))
  have hc := HasMultiplicativeReduction.multiplicativeReduction
    (R := S) (W := U.map (algebraMap S L))
  rw [map_Δ, valuation_lt_one_iff_mem] at hd
  rw [map_c₄, valuation_eq_one_iff_notMem] at hc
  constructor
  · rw [fractionValuationEquation, map_Δ]
    have h := (ringEquiv_mem_maximalIdeal_pow_iff
      (fractionValuationEquiv S L) U.Δ 1).mpr (by rw [pow_one]; exact hd)
    rw [pow_one] at h
    exact h
  · rw [fractionValuationEquation, map_c₄]
    exact ((notMem_maximalIdeal).mp hc).map _

/-- Generic ellipticity is preserved with the exact original variable change. -/
theorem fractionValuationEquation_generic_isElliptic (E : WeierstrassCurve L)
    [E.IsElliptic] (C : VariableChange L) (hC : C • E = U.map (algebraMap S L)) :
    ((V).map (algebraMap A L)).IsElliptic := by
  rw [fractionValuationEquation_generic, ← hC]
  infer_instance

end FLT.Mazur
