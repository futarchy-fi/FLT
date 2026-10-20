/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedTangentBranchSpecialFiber
public import FLT.Mazur.WeierstrassDividedTangentBranchSpecializedZero

/-!
# Full input-scale congruences for the actual branch output

Cleared output residues give divisibility by the entire input scale, not just
vanishing on the closed fiber. These identities can be divided by a smaller
refinement scale to detect nonzero intermediate output residues.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.WeierstrassDilatation
open WeierstrassCurve
section Specialization
variable {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
  (W : WeierstrassCurve R) (s b3 a2 b4' b6' u₁ u₂ v₁ v₂ : R)
  (hc : IsUnit (v₁ + W.a₁ * u₁ + b3))
  (hd : IsUnit (v₁ + v₂ + W.a₁ * u₂ + b3))
local notation "k" => tangentBranchSlope W b3 a2 b4' b6' u₁ u₂ v₁ v₂ hc hd
local notation "X" => tangentBranchX W s a2 u₁ u₂ k
local notation "Y" => tangentBranchY W s b3 a2 u₁ u₂ v₁ k

/-- The output product and opposite-branch relation survive any specialization. -/
theorem tangentBranch_specialized_products
    (hs : f s = 0) (h3 : f b3 = 0) (h₁ : f v₁ = 0) (h₂ : f v₂ = 0) :
    f u₁ * f u₂ * f X = -f b6' ∧ f Y = -f W.a₁ * f X := by
  have hc' : IsUnit (f v₁ + (W.map f).a₁ * f u₁ + f b3) := by
    simpa only [map_add, map_mul, map_a₁] using hc.map f
  have hd' : IsUnit (f v₁ + f v₂ + (W.map f).a₁ * f u₂ + f b3) := by
    simpa only [map_add, map_mul, map_a₁] using hd.map f
  have hx := tangentBranchX_residue (W.map f) (f s) (f b3) (f a2) (f b4') (f b6')
    (f u₁) (f u₂) (f v₁) (f v₂) hc' hd' hs h3 h₁ h₂
  rw [← tangentBranchX_map f W s b3 a2 b4' b6' u₁ u₂ v₁ v₂ hc hd hc' hd'] at hx
  refine ⟨hx, ?_⟩
  have hy := tangentBranchY_residue (W.map f) (f s) (f b3) (f a2) (f b4') (f b6')
    (f u₁) (f u₂) (f v₁) (f v₂) hc' hd' hs h3 h₁
  rw [← tangentBranchX_map f W s b3 a2 b4' b6' u₁ u₂ v₁ v₂ hc hd hc' hd',
    ← tangentBranchY_map f W s b3 a2 b4' b6' u₁ u₂ v₁ v₂ hc hd hc' hd'] at hy
  exact hy

end Specialization

section Divisibility
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
local notation "v₁" => ((j).comp a) (y W s b3 b4 b6)
local notation "v₂" => ((j).comp c) (y W s b3 b4 b6)
local notation "q" => algebraMap R B s
local notation "W'" => W.map (algebraMap R B)
local notation "b3B" => algebraMap R B b3
variable (a2 b4' b6' : R)
  (h2 : W.a₂ = s * a2) (h4' : b4 = s * b4') (h6' : b6 = s * b6')
  (h3 : s ∣ b3)
local notation "X" => dividedTangentBranchX W s b3 b4 b6 a c a2 b4' b6'
local notation "Y" => dividedTangentBranchY W s b3 b4 b6 a c a2 b4' b6'

include h2 h4' h6' h3 in
/-- The branch product and opposite-branch errors are divisible by the full input scale. -/
theorem dividedTangentBranch_products_dvd :
    q ∣ u₁ * u₂ * X + algebraMap R B b6' ∧ q ∣ Y + (W').a₁ * X := by
  let I : Ideal B := Ideal.span {q}
  let f : B →+* B ⧸ I := Ideal.Quotient.mk I
  have hq : f q = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))
  have h3q : f b3B = 0 := by
    obtain ⟨w, hw⟩ := h3
    have he : b3B = q * algebraMap R B w := by
      simpa only [map_mul] using congrArg (algebraMap R B) hw
    rw [he, map_mul, hq, zero_mul]
  have hv := dividedTangentBranch_specialFiber_ordinates W s b3 b4 b6 a c
    a2 b4' b6' h2 h4' h6' f hq
  have hp := tangentBranch_specialized_products f W' q b3B
    (algebraMap R B a2) (algebraMap R B b4') (algebraMap R B b6') u₁ u₂ v₁ v₂
    (dividedTangentBranch_coordinate_units W s b3 b4 b6 a c).1
    (dividedTangentBranch_coordinate_units W s b3 b4 b6 a c).2 hq h3q hv.1 hv.2
  change f u₁ * f u₂ * f X = -f (algebraMap R B b6') ∧
    f Y = -f (W').a₁ * f X at hp
  constructor
  · apply Ideal.mem_span_singleton.mp
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    change f (u₁ * u₂ * X + algebraMap R B b6') = 0
    simp only [map_add, map_mul, hp.1, neg_add_cancel]
  · apply Ideal.mem_span_singleton.mp
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    change f (Y + (W').a₁ * X) = 0
    simp only [map_add, map_mul, hp.2, neg_mul, neg_add_cancel]

end Divisibility
end FLT.Mazur.WeierstrassDilatation
