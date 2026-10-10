/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticAdditiveScalingDepth
public import FLT.Mazur.EllipticExtensionScalingDescent
public import FLT.Mazur.EllipticSemistableExtension
public import FLT.Mazur.EllipticValuationRingEquation
public import FLT.Mazur.FiniteDVRComplete
public import FLT.Mazur.ValuationRingCompleteModel
public import FLT.Mazur.ValuationRingHenselianModel

/-!
# Smooth torsion on additive short equations over an unramified base

The actual fourth or sixth root extension has absolute ramification at most
six. Its positive short scaling contradicts smooth reduction of the original
prime-torsion point. This includes torsion at the residue prime itself.
-/

@[expose] public section

namespace FLT.Mazur

open WeierstrassCurve IsLocalRing

variable {K : Type*} [Field K] (A : ValuationSubring K)
  [IsDiscreteValuationRing A] [IsAdicComplete (maximalIdeal A) A]

/-- Smooth prime torsion on a short additive equation vanishes at an unramified prime ≥ 17. -/
theorem short_smooth_prime_torsion_eq_zero_unramified
    (p : ℕ) [Fact p.Prime] [CharP (ResidueField A) p]
    (hp : Irreducible (p : A)) (hp17 : 17 ≤ p)
    (W : WeierstrassCurve A) [W.IsShortNF] (hΔ : W.Δ ≠ 0)
    (hd : W.Δ ∈ maximalIdeal A) (hc : W.c₄ ∈ maximalIdeal A)
    (P : (W.map (algebraMap A K)).toProjective.Point) (hP : p • P = 0)
    (hsm : SmoothReduction A W P) : P = 0 := by
  classical
  obtain ⟨h2, h3⟩ := two_three_units_of_residue_char_gt_three (R := A) p (by omega)
  obtain ⟨L, hL, aK, fin, aR, towerK, S, hS, dom, dvr, aS, finS, aSL, towerS,
    frac, closure, e, m, ρ, U, C, he, _, hρ, _, hval, _, _, hs, hCu,
    hCr, hCs, hCt, _, _, hC⟩ :=
    exists_short_semistable_extension_scaling (K := K) W hΔ h2 h3 hp
  have hinj : Function.Injective (algebraMap A L) := by
    rw [IsScalarTower.algebraMap_eq A K L]
    exact (algebraMap K L).injective.comp (IsFractionRing.injective A K)
  let _ : FaithfulSMul A S := (faithfulSMul_iff_algebraMap_injective A S).mpr (by
    intro x y hxy
    apply hinj
    rw [IsScalarTower.algebraMap_apply A S L, IsScalarTower.algebraMap_apply A S L, hxy])
  let _ : IsAdicComplete (maximalIdeal S) S := finiteDVR_isAdicComplete (R := A)
  let B := fractionValuationSubring S L
  let _ : IsDiscreteValuationRing B := fractionValuationSubring_isDiscreteValuationRing S L
  let _ : IsAdicComplete (maximalIdeal B) B := fractionValuationSubring_isAdicComplete S L
  let g : A →+* B := fractionValuationBaseMap
  have hcompat : (algebraMap B L).comp g =
      (algebraMap K L).comp (algebraMap A K) := by
    ext x
    exact (fractionValuationBaseMap_coe x).trans (IsScalarTower.algebraMap_apply A K L x)
  have hmap : (W.map g).map (algebraMap B L) = W.map (algebraMap A L) := by
    rw [map_map]
    congr 1
    ext x
    exact fractionValuationBaseMap_coe x
  let _ : ((W.map g).map (algebraMap B L)).IsElliptic := by
    rw [hmap, isElliptic_iff, map_Δ, isUnit_iff_ne_zero]
    exact fun h => hΔ (hinj (h.trans (map_zero _).symm))
  have hm := short_additive_scaling_exponent_pos (algebraMap A S) W h2 h3 hd hc m hs
  let u : B := fractionValuationEquiv S L (ρ ^ m)
  have hu : u ∈ maximalIdeal B := by
    have hn : ρ ^ m ∈ maximalIdeal S := Ideal.pow_mem_of_mem _ hρ.not_isUnit m hm
    simpa only [pow_one] using (ringEquiv_mem_maximalIdeal_pow_iff
      (fractionValuationEquiv S L) (ρ ^ m) 1).mpr (by simpa only [pow_one] using hn)
  have hpS : (p : S) ≠ 0 := by
    simpa only [map_natCast, map_zero] using
      (FaithfulSMul.algebraMap_injective A S).ne hp.ne_zero
  have hpB : (p : B) ≠ 0 := by
    simpa only [map_natCast, map_zero] using (fractionValuationEquiv S L).injective.ne hpS
  have horder : RaynaudParameters.order (p : B) < p - 1 := by
    rw [fractionValuationSubring_prime_order]
    have ho : RaynaudParameters.order (p : S) = e := by
      simpa only [RaynaudParameters.order, map_natCast, ENat.toNat_natCast] using
        congrArg ENat.toNat hval
    rw [ho]
    rcases he with rfl | rfl <;> omega
  obtain ⟨h4, _⟩ := short_additive_coefficients_mem W h2 h3 hd hc
  apply smooth_prime_torsion_eq_zero_of_extension_scaling A B W (algebraMap K L) g hcompat
    (by simp only [map_a₃, a₃_of_isShortNF, map_zero]; exact Ideal.zero_mem _)
    (show ¬ IsUnit (g W.a₄) from fun h => h4 (IsLocalHom.map_nonunit (f := g) _ h))
    (fractionValuationEquation (L := L) U) p hpB horder u hu C
    (by rw [hmap, fractionValuationEquation_generic]; exact hC)
    hCu hCr hCs hCt P hP hsm

end FLT.Mazur
