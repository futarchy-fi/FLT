/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.Polynomial.GaussLemma
public import Mathlib.RingTheory.Valuation.LocalSubring

/-!
# Lifting residue roots over an algebraically closed valued field

Every root of a nonzero reduced polynomial lifts to a root in the valuation ring.
The polynomial need not be monic and its residue root need not be simple. This applies
in particular to division polynomials at the residue characteristic.

The proof removes one generic root at a time. An integral root gives a factor `X - a`.
A nonintegral root gives the primitive factor `a⁻¹ X - 1`, whose reduction is a unit;
Gauss's lemma descends its complementary factor to the valuation ring.
-/

@[expose] public section

open Polynomial IsLocalRing
namespace ValuationSubring

variable {K : Type*} [Field K] [IsAlgClosed K] (A : ValuationSubring K)

/-- Every root of a nonzero reduced polynomial lifts over an algebraically closed valued field.
Neither monicity nor simplicity of the residue root is required. -/
theorem exists_root_lifting (f : A[X]) (hzero : f.map (residue A) ≠ 0)
    (b : ResidueField A) (hb : (f.map (residue A)).IsRoot b) :
    ∃ a : A, f.IsRoot a ∧ residue A a = b := by
  classical
  induction hd : f.natDegree using Nat.strong_induction_on generalizing f with
  | h n ih =>
    have hf : f ≠ 0 := fun h => hzero (by simp [h])
    have hpos : 0 < f.natDegree := by
      by_contra! h
      have he := eq_C_of_natDegree_eq_zero (Nat.eq_zero_of_le_zero h)
      rw [he] at hb hzero
      simp only [Polynomial.map_C, IsRoot, eval_C] at hb
      exact hzero (by simp [hb])
    obtain ⟨x, hx⟩ := IsAlgClosed.exists_root (f.map (algebraMap A K)) (by
      have hmap : f.map (algebraMap A K) ≠ 0 := by
        simpa only [Polynomial.map_zero] using
          (Polynomial.map_injective _ (IsFractionRing.injective A K)).ne hf
      rw [degree_eq_natDegree hmap,
        natDegree_map_eq_of_injective (IsFractionRing.injective A K)]
      exact_mod_cast hpos.ne')
    by_cases hmem : x ∈ A
    · let a : A := ⟨x, hmem⟩
      have ha : f.IsRoot a := by
        apply (IsFractionRing.injective A K)
        simpa only [map_zero, ← eval₂_at_apply, ← eval_map] using
          (show (f.map (algebraMap A K)).eval (algebraMap A K a) = 0 from hx)
      obtain ⟨g, hg⟩ := dvd_iff_isRoot.mpr ha
      have hg0 : g ≠ 0 := by
        intro hz
        exact hf (by simpa only [hz, mul_zero] using hg)
      have hdeg : g.natDegree < f.natDegree := by
        rw [hg, natDegree_mul (X_sub_C_ne_zero a) hg0, natDegree_X_sub_C]
        omega
      have hb' : b - residue A a = 0 ∨ (g.map (residue A)).eval b = 0 := by
        simpa only [hg, Polynomial.map_mul, Polynomial.map_sub, map_X, Polynomial.map_C,
          IsRoot, eval_mul, eval_sub, eval_X, eval_C, mul_eq_zero] using hb
      rcases hb' with he | he
      · exact ⟨a, ha, (sub_eq_zero.mp he).symm⟩
      · have hgzero : g.map (residue A) ≠ 0 := by
          intro hz
          exact hzero (by rw [hg, Polynomial.map_mul, hz, mul_zero])
        obtain ⟨c, hc, hcb⟩ := ih g.natDegree (hd ▸ hdeg) g hgzero he rfl
        exact ⟨c, by simp [hg, IsRoot, hc.eq_zero], hcb⟩
    · have hx0 : x ≠ 0 := by intro h; exact hmem (h ▸ A.zero_mem)
      let a : A := ⟨x⁻¹, (A.mem_or_inv_mem x).resolve_left hmem⟩
      let l : A[X] := C a * X - 1
      have hlprim : l.IsPrimitive := by
        intro c hc
        have hh := ((C_dvd_iff_dvd_coeff c l).mp hc) 0
        have hcunit : IsUnit (- (1 : A)) := isUnit_one.neg
        exact isUnit_of_dvd_unit (by simpa [l] using hh) hcunit
      have hlmap : l.map (algebraMap A K) = C x⁻¹ * (X - C x) := by
        simp only [l, Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_C,
          map_X, Polynomial.map_one]
        change C x⁻¹ * X - 1 = _
        rw [mul_sub, ← C_mul, inv_mul_cancel₀ hx0, C_1]
      obtain ⟨g, hg⟩ := hlprim.dvd_of_fraction_map_dvd_fraction_map (K := K) (q := f) (by
        rw [hlmap]
        obtain ⟨q, hq⟩ := dvd_iff_isRoot.mpr hx
        refine ⟨C x * q, ?_⟩
        calc
          _ = (X - C x) * q := hq
          _ = (C x⁻¹ * C x) * ((X - C x) * q) := by
            rw [← C_mul, inv_mul_cancel₀ hx0, C_1, one_mul]
          _ = _ := by ring)
      have hl0 : l ≠ 0 := hlprim.ne_zero
      have hg0 : g ≠ 0 := by
        intro hz
        exact hf (by simpa only [hz, mul_zero] using hg)
      have ha0 : a ≠ 0 := by
        intro h
        have hh := congrArg (fun z : A => (z : K)) h
        exact (inv_ne_zero hx0) hh
      have hdeg : g.natDegree < f.natDegree := by
        rw [hg, natDegree_mul hl0 hg0]
        have hl : l.natDegree = 1 := by
          change (C a * X - C 1).natDegree = 1
          rw [natDegree_sub_C, natDegree_C_mul_X a ha0]
        omega
      have hares : residue A a = 0 := by
        rw [residue_eq_zero_iff, ← coe_mem_nonunits_iff]
        exact A.inv_mem_nonunits_iff.mpr (Or.inr hmem)
      have hlres : l.map (residue A) = -1 := by simp [l, hares]
      have hgroot : (g.map (residue A)).IsRoot b := by
        simpa [hg, Polynomial.map_mul, hlres, IsRoot] using hb
      have hgzero : g.map (residue A) ≠ 0 := by
        intro hz
        exact hzero (by rw [hg, Polynomial.map_mul, hz, mul_zero])
      obtain ⟨c, hc, hcb⟩ := ih g.natDegree (hd ▸ hdeg) g hgzero hgroot rfl
      exact ⟨c, by simp [hg, IsRoot, hc.eq_zero], hcb⟩

end ValuationSubring
