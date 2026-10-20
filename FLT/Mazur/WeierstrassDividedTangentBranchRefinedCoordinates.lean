/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedTangentBranchSpecialFiber
public import FLT.Mazur.WeierstrassDividedTangentBranchSpecializedZero

/-!
# Divide strict-branch outputs by any admissible intermediate scale

Any common divisor of the input scale, third coefficient and first constant
quotient divides both output coordinates. This permits refinement by the
remaining node depth even when that depth is smaller than the input depth.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.WeierstrassDilatation
open WeierstrassCurve
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

variable (t : R) (hts : t ∣ s) (ht3 : t ∣ b3) (ht6 : t ∣ b6')
local notation "q'" => algebraMap R B t
local notation "X" => dividedTangentBranchX W s b3 b4 b6 a c a2 b4' b6'
local notation "Y" => dividedTangentBranchY W s b3 b4 b6 a c a2 b4' b6'

include h2 h4' h6' hts ht3 ht6 in
/-- Both branch outputs are divisible by the intermediate scale in the original source ring. -/
theorem dividedTangentBranch_refined_divisibility : q' ∣ X ∧ q' ∣ Y := by
  let I : Ideal B := Ideal.span {q'}
  let f : B →+* B ⧸ I := Ideal.Quotient.mk I
  have ht : f q' = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))
  have kill (z : R) (hz : t ∣ z) : f (algebraMap R B z) = 0 := by
    obtain ⟨w, hw⟩ := hz
    rw [hw, map_mul, map_mul, ht, zero_mul]
  have hq : f q = 0 := kill s hts
  have hv := dividedTangentBranch_specialFiber_ordinates W s b3 b4 b6 a c
    a2 b4' b6' h2 h4' h6' f hq
  have h3q : f b3B = 0 := kill b3 ht3
  have h6q : f (algebraMap R B b6') = 0 := kill b6' ht6
  have h := tangentBranch_specialized_zero f W' q b3B
    (algebraMap R B a2) (algebraMap R B b4') (algebraMap R B b6') u₁ u₂ v₁ v₂
    (dividedTangentBranch_coordinate_units W s b3 b4 b6 a c).1
    (dividedTangentBranch_coordinate_units W s b3 b4 b6 a c).2 hq h3q hv.1 hv.2 h6q
  exact ⟨Ideal.mem_span_singleton.mp (Ideal.Quotient.eq_zero_iff_mem.mp h.1),
    Ideal.mem_span_singleton.mp (Ideal.Quotient.eq_zero_iff_mem.mp h.2)⟩

/-- Construct the next divided abscissa from proved ideal membership. -/
def dividedTangentBranchRefinedX : B :=
  (dividedTangentBranch_refined_divisibility W s b3 b4 b6 a c a2 b4' b6'
    h2 h4' h6' t hts ht3 ht6).1.choose

/-- Construct the next divided ordinate from proved ideal membership. -/
def dividedTangentBranchRefinedY : B :=
  (dividedTangentBranch_refined_divisibility W s b3 b4 b6 a c a2 b4' b6'
    h2 h4' h6' t hts ht3 ht6).2.choose

/-- Scaling the constructed next abscissa recovers the actual first divided output. -/
theorem dividedTangentBranchRefinedX_mul :
    q' * dividedTangentBranchRefinedX W s b3 b4 b6 a c a2 b4' b6'
      h2 h4' h6' t hts ht3 ht6 = X :=
  (dividedTangentBranch_refined_divisibility W s b3 b4 b6 a c a2 b4' b6'
    h2 h4' h6' t hts ht3 ht6).1.choose_spec.symm

/-- Scaling the constructed next ordinate recovers the actual first divided output. -/
theorem dividedTangentBranchRefinedY_mul :
    q' * dividedTangentBranchRefinedY W s b3 b4 b6 a c a2 b4' b6'
      h2 h4' h6' t hts ht3 ht6 = Y :=
  (dividedTangentBranch_refined_divisibility W s b3 b4 b6 a c a2 b4' b6'
    h2 h4' h6' t hts ht3 ht6).2.choose_spec.symm

end FLT.Mazur.WeierstrassDilatation
