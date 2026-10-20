/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedTangentBranchMap
public import FLT.Mazur.WeierstrassDividedTangentBranchResidueUnit

/-!
# Vanishing of nonterminal branch outputs after specialization

When the next constant coefficient also vanishes, both constructed output
coordinates vanish. Unit branch factors provide cancellation over any ring.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.WeierstrassDilatation
open WeierstrassCurve
variable {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
  (W : WeierstrassCurve R) (s b3 a2 b4' b6' u₁ u₂ v₁ v₂ : R)
  (hc : IsUnit (v₁ + W.a₁ * u₁ + b3))
  (hd : IsUnit (v₁ + v₂ + W.a₁ * u₂ + b3))
local notation "k" => tangentBranchSlope W b3 a2 b4' b6' u₁ u₂ v₁ v₂ hc hd
local notation "X" => tangentBranchX W s a2 u₁ u₂ k
local notation "Y" => tangentBranchY W s b3 a2 u₁ u₂ v₁ k

/-- A nonterminal strict-branch output vanishes in both divided coordinates. -/
theorem tangentBranch_specialized_zero
    (hs : f s = 0) (h3 : f b3 = 0) (h₁ : f v₁ = 0) (h₂ : f v₂ = 0)
    (h6 : f b6' = 0) : f X = 0 ∧ f Y = 0 := by
  have hc' : IsUnit (f v₁ + (W.map f).a₁ * f u₁ + f b3) := by
    simpa only [map_add, map_mul, map_a₁] using hc.map f
  have hd' : IsUnit (f v₁ + f v₂ + (W.map f).a₁ * f u₂ + f b3) := by
    simpa only [map_add, map_mul, map_a₁] using hd.map f
  have hu := tangentBranch_residue_input_units (W.map f) (f b3)
    (f u₁) (f u₂) (f v₁) (f v₂) hc' hd' h3 h₁ h₂
  have hx := tangentBranchX_residue (W.map f) (f s) (f b3) (f a2) (f b4') (f b6')
    (f u₁) (f u₂) (f v₁) (f v₂) hc' hd' hs h3 h₁ h₂
  rw [← tangentBranchX_map f W s b3 a2 b4' b6' u₁ u₂ v₁ v₂ hc hd hc' hd', h6,
    neg_zero] at hx
  have hx0 : f X = 0 := (hu.2.1.mul hu.2.2).mul_right_inj.mp (by
    simpa only [mul_zero] using hx)
  refine ⟨hx0, ?_⟩
  have hy := tangentBranchY_residue (W.map f) (f s) (f b3) (f a2) (f b4') (f b6')
    (f u₁) (f u₂) (f v₁) (f v₂) hc' hd' hs h3 h₁
  rw [← tangentBranchX_map f W s b3 a2 b4' b6' u₁ u₂ v₁ v₂ hc hd hc' hd',
    ← tangentBranchY_map f W s b3 a2 b4' b6' u₁ u₂ v₁ v₂ hc hd hc' hd', hx0,
    mul_zero] at hy
  exact hy

end FLT.Mazur.WeierstrassDilatation
