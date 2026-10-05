/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticShortSemistableExtension
public import FLT.Mazur.EllipticUnitInvariantsReduction
public import FLT.Mathlib.RingTheory.DiscreteValuationRing.TotalRamification

/-!
# Semistable extension of ramification degree at most six

When two and three are units, put the integral equation in short normal
form, adjoin a fourth or sixth root of a uniformizer, and scale to the first
unit coefficient. The output is an actual minimal good or multiplicative
model over a finite extension, with the ideal ramification index at most six.
-/

@[expose] public section

namespace FLT.Mazur

open WeierstrassCurve IsLocalRing IsDiscreteValuationRing

universe u

variable {R K : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable [Field K] [Algebra R K] [IsFractionRing R K]

/-- Residue characteristic greater than three makes the short-normal-form denominators units. -/
theorem two_three_units_of_residue_char_gt_three (q : ℕ) [CharP (ResidueField R) q]
    (hq : 3 < q) : IsUnit (2 : R) ∧ IsUnit (3 : R) := by
  have hu (n : ℕ) (hn : 0 < n) (hnq : n < q) : IsUnit (n : R) := by
    apply (residue_ne_zero_iff_isUnit _).mp
    rw [map_natCast]
    apply (CharP.cast_eq_zero_iff (ResidueField R) q n).not.mpr
    intro hd
    exact (not_le_of_gt hnq) (Nat.le_of_dvd hn hd)
  exact ⟨hu 2 (by decide) (by omega), hu 3 (by decide) hq⟩

/-- Construct an actual semistable model after an extension of degree and ramification
at most six. -/
theorem exists_semistable_extension_of_two_three_units (W : WeierstrassCurve R)
    (hΔ : W.Δ ≠ 0) (h2 : IsUnit (2 : R)) (h3 : IsUnit (3 : R)) :
    ∃ (L : Type u) (_ : Field L) (_ : Algebra K L) (_ : FiniteDimensional K L)
      (_ : Algebra R L) (_ : IsScalarTower R K L) (S : Type u) (_ : CommRing S)
      (_ : IsDomain S) (_ : IsDiscreteValuationRing S) (_ : Algebra R S)
      (_ : Module.Finite R S) (_ : Algebra S L) (_ : IsScalarTower R S L)
      (_ : IsFractionRing S L) (_ : IsIntegralClosure S R L)
      (U : WeierstrassCurve S) (C : VariableChange L),
      Module.finrank K L ≤ 6 ∧ (IsLocalRing.maximalIdeal S).ramificationIdx R ≤ 6 ∧
      ((U.map (algebraMap S L)).HasGoodReduction S ∨
        (U.map (algebraMap S L)).HasMultiplicativeReduction S) ∧
      C • W.map (algebraMap R L) = U.map (algebraMap S L) := by
  let : Invertible (2 : R) := h2.invertible
  let : Invertible (3 : R) := h3.invertible
  let D := W.toShortNF
  let V := D • W
  have : V.IsShortNF := W.toShortNF_spec
  have hV : V.Δ ≠ 0 := by
    rw [show V.Δ = (↑(D.u⁻¹) : R) ^ 12 * W.Δ from variableChange_Δ W D]
    exact mul_ne_zero (pow_ne_zero 12 (Units.ne_zero _)) hΔ
  obtain ⟨π, hπ⟩ := exists_irreducible R
  obtain ⟨L, hL, aK, fin, aR, towerK, S, hS, dom, dvr, aS, finS, aSL, towerS,
    frac, closure, U, C, hdeg, hval, _, hu, hC⟩ :=
    exists_short_semistable_extension (K := K) V hV h2 h3 hπ
  have hinj : Function.Injective (algebraMap R L) := by
    rw [IsScalarTower.algebraMap_eq R K L]
    exact (algebraMap K L).injective.comp (IsFractionRing.injective R K)
  have : FaithfulSMul R S := (faithfulSMul_iff_algebraMap_injective R S).mpr (by
    intro x y hxy
    apply hinj
    rw [IsScalarTower.algebraMap_apply R S L, IsScalarTower.algebraMap_apply R S L, hxy])
  have hi : (IsLocalRing.maximalIdeal S).ramificationIdx R = Module.finrank K L := by
    apply ENat.natCast_inj.mp
    exact (addValMapUniformizerEqRamificationIdx (S := S) hπ).symm.trans hval
  refine ⟨L, hL, aK, fin, aR, towerK, S, hS, dom, dvr, aS, finS, aSL, towerS,
    frac, closure, U, C * D.map (algebraMap R L), hdeg, hi ▸ hdeg,
    good_or_multiplicative_of_unit_invariants U hu, ?_⟩
  rw [mul_smul, map_variableChange]
  exact hC

end FLT.Mazur
