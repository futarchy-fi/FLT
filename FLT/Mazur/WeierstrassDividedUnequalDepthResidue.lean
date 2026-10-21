/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedUnequalDepthOutput
public import FLT.Mazur.WeierstrassDividedUnequalSecantResidue
public import FLT.Mazur.WeierstrassDividedVerticalSmooth

/-!
# Specializing the actual unequal-depth output

The opposite-branch computation applies to the constructed algebra map over
any residue field. The derivative tested here is at the difference-depth
output, rather than at either input's singular common-depth contraction.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassDilatation WeierstrassCurve
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R S K : Type u} [CommRing R] [CommRing S] [Field K]
  [Algebra R S] [Algebra R K] [IsDomain R] [Module.Flat R S]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {k l : ℕ}
  (d : Data W π k) (e : Data W π l) (hkl : k ≤ l) (z : Data W π (l - k))
  (a : Coordinate W (π ^ k) d.b3 d.b4 d.b6 →ₐ[R] S)
  (c : Coordinate W (π ^ l) e.b3 e.b4 e.b6 →ₐ[R] S)
local notation "T" => UnequalDepthSecantRing hπ d e hkl a c
local notation "j" => IsScalarTower.toAlgHom R S T
variable (ρ : UnequalDepthSecantRing hπ d e hkl a c →ₐ[R] K)
local notation "x₁" => ρ (((j).comp a) (x W (π ^ k) d.b3 d.b4 d.b6))
local notation "y₁" => ρ (((j).comp a) (y W (π ^ k) d.b3 d.b4 d.b6))
local notation "x₂" => ρ (((j).comp c) (x W (π ^ l) e.b3 e.b4 e.b6))
local notation "y₂" => ρ (((j).comp c) (y W (π ^ l) e.b3 e.b4 e.b6))
local notation "α" => algebraMap R K W.a₁
local notation "c₀" => unequalDepthRight hπ d e hkl c
local notation "dx" => a (x W (π ^ k) d.b3 d.b4 d.b6) - c₀ (x W (π ^ k) d.b3 d.b4 d.b6)
local notation "i" => ρ (IsLocalization.Away.invSelf dx : T)
local notation "slope" => ρ (dividedSecantSlope W (π ^ k) d.b3 d.b4 d.b6 a c₀)
local notation "X" => unequalDepthSecantX hπ d e hkl a c
local notation "Y" => unequalDepthSecantY hπ d e hkl a c
local notation "W'" => W.map (algebraMap R K)
local notation "X₀" => unequalSecantX W' 0 0 0 0 0 x₁ y₁ x₂ y₂ i
local notation "Y₀" => unequalSecantY W' 0 0 0 0 0 x₁ y₁ x₂ y₂ i slope
variable (hs : algebraMap R K (π ^ k) = 0) (ht : algebraMap R K (π ^ (l - k)) = 0)
  (h3 : algebraMap R K e.b3 = 0) (h4 : algebraMap R K e.b4 = 0)
  (h6 : algebraMap R K e.b6 = 0)

include hs ht h3 h4 h6

omit [Module.Flat R S] in
/-- Specialization of the actual abscissa is the explicit residue formula. -/
theorem unequalDepthSecantX_residue : ρ X = X₀ := by
  simp only [map_pow] at hs ht
  simp only [unequalDepthSecantX, unequalSecantX, unequalSecantNumerator,
    map_add, map_mul, map_sub, map_neg, map_pow, map_ofNat, map_a₁, map_a₂,
    AlgHom.commutes, hs, ht, h3, h4, h6]

omit [Module.Flat R S] in
/-- Specialization of the actual ordinate uses the same residue secant slope. -/
theorem unequalDepthSecantY_residue : ρ Y = Y₀ := by
  simp only [map_pow] at hs ht
  simp only [unequalDepthSecantY, unequalSecantY, unequalSecantX, unequalSecantNumerator,
    map_add, map_mul, map_sub, map_neg, map_pow, map_ofNat, map_a₁, map_a₂,
    AlgHom.commutes, hs, ht, h3, h4, h6]

/-- Both opposite-branch orientations give a vertically smooth actual divided output. -/
theorem unequalDepthSecantOutput_residue_vertical
    (h2 : algebraMap R K W.a₂ = 0) (ha : α ≠ 0) (hz : algebraMap R K z.b3 = 0)
    (hu : x₂ ≠ 0)
    (hbranch : (y₁ = 0 ∧ y₂ = -α * x₂) ∨ (y₁ = -α * x₁ ∧ y₂ = 0)) :
    ρ (unequalDepthSecantOutput hπ d e hkl z a c
      (verticalDerivative W (π ^ (l - k)) z.b3 z.b4 z.b6)) ≠ 0 := by
  have hi := congrArg ρ (unequalDepthSecant_inverse hπ d e hkl a c)
  have hl := congrArg ρ (unequalDepthSecant_chord hπ d e hkl a c)
  simp only [map_mul, map_sub, map_one, AlgHom.commutes, ht, zero_mul, sub_zero] at hi hl
  have hn := unequalSecant_residue_vertical W' x₁ y₁ x₂ y₂ i slope h2 ha hi hl hu hbranch
  simpa only [verticalDerivative_eq, map_add, map_mul, map_ofNat, AlgHom.commutes,
    unequalDepthSecantOutput_x, unequalDepthSecantOutput_y, hz, add_zero,
    unequalDepthSecantX_residue hπ d e hkl a c ρ hs ht h3 h4 h6,
    unequalDepthSecantY_residue hπ d e hkl a c ρ hs ht h3 h4 h6, map_a₁] using hn

end FLT.Mazur.WeierstrassDividedDepth
