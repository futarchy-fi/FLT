/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedTangentBranchProductCongruence
public import FLT.Mazur.WeierstrassDividedTangentBranchRefinedCoordinates

/-!
# Cancel the refinement scale in branch product congruences

Flatness makes the refinement scale regular on the actual branch source.
The divided coordinates therefore retain congruences modulo the remaining
input scale, even when the refinement scale vanishes in the residue ring.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.WeierstrassDilatation
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
  (W : WeierstrassCurve R) (s b3 b4 b6 : R)
  (a c : Coordinate W s b3 b4 b6 →ₐ[R] S)
local notation "B" => DividedTangentBranchRing W s b3 b4 b6 a c
local notation "j" => IsScalarTower.toAlgHom R S B
local notation "u₁" => ((j).comp a) (x W s b3 b4 b6)
local notation "u₂" => ((j).comp c) (x W s b3 b4 b6)
variable (a2 b4' b6' : R)
  (h2 : W.a₂ = s * a2) (h4' : b4 = s * b4') (h6' : b6 = s * b6')
  (t : R) (hts : t ∣ s) (ht3 : t ∣ b3) (ht6 : t ∣ b6')
local notation "Xr" => dividedTangentBranchRefinedX W s b3 b4 b6 a c
  a2 b4' b6' h2 h4' h6' t hts ht3 ht6
local notation "Yr" => dividedTangentBranchRefinedY W s b3 b4 b6 a c
  a2 b4' b6' h2 h4' h6' t hts ht3 ht6
variable [Module.Flat R S] (hs : IsRegular s) (h3 : s ∣ b3)
  (w beta : R) (hw : s = t * w) (hb : b6' = t * beta)

include hs h3 hw hb in
/-- Cancellation leaves the exact refined product errors divisible by the scale quotient. -/
theorem dividedTangentBranchRefined_products_dvd :
    algebraMap R B w ∣ u₁ * u₂ * Xr + algebraMap R B beta ∧
      algebraMap R B w ∣ Yr + algebraMap R B W.a₁ * Xr := by
  have hp := dividedTangentBranch_products_dvd W s b3 b4 b6 a c
    a2 b4' b6' h2 h4' h6' h3
  have hx := dividedTangentBranchRefinedX_mul W s b3 b4 b6 a c
    a2 b4' b6' h2 h4' h6' t hts ht3 ht6
  have hy := dividedTangentBranchRefinedY_mul W s b3 b4 b6 a c
    a2 b4' b6' h2 h4' h6' t hts ht3 ht6
  have ht : IsRegular t := (hw ▸ hs).of_mul_left
  have htB : IsRegular (algebraMap R B t) :=
    WeierstrassIntegralChart.flatRingHom_isRegular _
      (RingHom.flat_algebraMap_iff.mpr inferInstance) ht
  obtain ⟨z, hz⟩ := hp.1
  obtain ⟨v, hv⟩ := hp.2
  have hwB : algebraMap R B s = algebraMap R B t * algebraMap R B w := by
    simp only [hw, map_mul]
  have hbB : algebraMap R B b6' = algebraMap R B t * algebraMap R B beta := by
    simp only [hb, map_mul]
  rw [← hx, hbB, hwB] at hz
  rw [← hx, ← hy, hwB, WeierstrassCurve.map_a₁] at hv
  constructor
  · refine ⟨z, htB.left ?_⟩
    linear_combination hz
  · refine ⟨v, htB.left ?_⟩
    linear_combination hv

include hs h3 hw hb in
/-- Every specialization killing the remaining scale sees the exact refined residues. -/
theorem dividedTangentBranchRefined_specialized_products
    {T : Type*} [CommRing T] (f : B →+* T) (hf : f (algebraMap R B w) = 0) :
    f u₁ * f u₂ * f Xr = -f (algebraMap R B beta) ∧
      f Yr = -f (algebraMap R B W.a₁) * f Xr := by
  have hp := dividedTangentBranchRefined_products_dvd W s b3 b4 b6 a c
    a2 b4' b6' h2 h4' h6' t hts ht3 ht6 hs h3 w beta hw hb
  obtain ⟨z, hz⟩ := hp.1
  obtain ⟨v, hv⟩ := hp.2
  have hz' := congrArg f hz
  have hv' := congrArg f hv
  simp only [map_add, map_mul, hf, zero_mul] at hz' hv'
  constructor
  · exact eq_neg_of_add_eq_zero_left hz'
  · rw [neg_mul]
    exact eq_neg_of_add_eq_zero_left hv'

end FLT.Mazur.WeierstrassDilatation
