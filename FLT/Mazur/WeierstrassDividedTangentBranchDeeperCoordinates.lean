/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedTangentBranchSpecialFiber
public import FLT.Mazur.WeierstrassDividedTangentBranchSpecializedZero

/-!
# Divide nonterminal strict-branch outputs once more

Vanishing in the quotient by the scale proves actual ideal membership in the
source ring. The next coordinates are chosen from proved divisibility, with
exact multiplication identities retaining the original output.
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

variable (b3' b6'' : R) (h3' : b3 = s * b3') (h6'' : b6' = s * b6'')
local notation "X" => dividedTangentBranchX W s b3 b4 b6 a c a2 b4' b6'
local notation "Y" => dividedTangentBranchY W s b3 b4 b6 a c a2 b4' b6'

include h2 h4' h6' h3' h6'' in
/-- Nonterminal branch outputs really are divisible by the scale in the original source ring. -/
theorem dividedTangentBranch_deeper_divisibility : q ∣ X ∧ q ∣ Y := by
  let I : Ideal B := Ideal.span {q}
  let f : B →+* B ⧸ I := Ideal.Quotient.mk I
  have hq : f q = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))
  have hv := dividedTangentBranch_specialFiber_ordinates W s b3 b4 b6 a c
    a2 b4' b6' h2 h4' h6' f hq
  have h3q : f b3B = 0 := by
    have he : b3B = q * algebraMap R B b3' := by simp only [h3', map_mul]
    rw [he, map_mul, hq, zero_mul]
  have h6q : f (algebraMap R B b6') = 0 := by
    have he : algebraMap R B b6' = q * algebraMap R B b6'' := by
      simp only [h6'', map_mul]
    rw [he, map_mul, hq, zero_mul]
  have h := tangentBranch_specialized_zero f W' q b3B
    (algebraMap R B a2) (algebraMap R B b4') (algebraMap R B b6') u₁ u₂ v₁ v₂
    (dividedTangentBranch_coordinate_units W s b3 b4 b6 a c).1
    (dividedTangentBranch_coordinate_units W s b3 b4 b6 a c).2 hq h3q hv.1 hv.2 h6q
  exact ⟨Ideal.mem_span_singleton.mp (Ideal.Quotient.eq_zero_iff_mem.mp h.1),
    Ideal.mem_span_singleton.mp (Ideal.Quotient.eq_zero_iff_mem.mp h.2)⟩

/-- Construct the next divided abscissa from proved ideal membership. -/
def dividedTangentBranchDeeperX : B :=
  (dividedTangentBranch_deeper_divisibility W s b3 b4 b6 a c a2 b4' b6'
    h2 h4' h6' b3' b6'' h3' h6'').1.choose

/-- Construct the next divided ordinate from proved ideal membership. -/
def dividedTangentBranchDeeperY : B :=
  (dividedTangentBranch_deeper_divisibility W s b3 b4 b6 a c a2 b4' b6'
    h2 h4' h6' b3' b6'' h3' h6'').2.choose

/-- Scaling the constructed next abscissa recovers the actual first divided output. -/
theorem dividedTangentBranchDeeperX_mul :
    q * dividedTangentBranchDeeperX W s b3 b4 b6 a c a2 b4' b6'
      h2 h4' h6' b3' b6'' h3' h6'' = X :=
  (dividedTangentBranch_deeper_divisibility W s b3 b4 b6 a c a2 b4' b6'
    h2 h4' h6' b3' b6'' h3' h6'').1.choose_spec.symm

/-- Scaling the constructed next ordinate recovers the actual first divided output. -/
theorem dividedTangentBranchDeeperY_mul :
    q * dividedTangentBranchDeeperY W s b3 b4 b6 a c a2 b4' b6'
      h2 h4' h6' b3' b6'' h3' h6'' = Y :=
  (dividedTangentBranch_deeper_divisibility W s b3 b4 b6 a c a2 b4' b6'
    h2 h4' h6' b3' b6'' h3' h6'').2.choose_spec.symm

end FLT.Mazur.WeierstrassDilatation
