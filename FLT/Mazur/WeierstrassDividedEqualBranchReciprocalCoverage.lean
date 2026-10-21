/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedReciprocalPrimeCoverage

/-!
# Opposite branches with equal abscissae have reciprocal outputs

The branch equations force a nonzero ordinate difference. This covers the
equal-depth case without positive-depth, pre-middle, or sum-depth bounds.
-/

@[expose] public noncomputable section
open AlgebraicGeometry
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassDilatation
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
  {W : WeierstrassCurve R} {π : R} {k : ℕ} (d : Data W π k)
  (a c : Coordinate W (π ^ k) d.b3 d.b4 d.b6 →ₐ[R] S)
local notation "x₁" => a (x W (π ^ k) d.b3 d.b4 d.b6)
local notation "x₂" => c (x W (π ^ k) d.b3 d.b4 d.b6)
local notation "y₁" => a (y W (π ^ k) d.b3 d.b4 d.b6)
local notation "y₂" => c (y W (π ^ k) d.b3 d.b4 d.b6)
local notation "α" => algebraMap R S W.a₁

/-- Opposite punctured branches with equal residue abscissae lie in the reciprocal domain. -/
theorem suppliedReciprocalDomain_opposite_mem (hα : IsUnit W.a₁) (p : PrimeSpectrum S)
    (hx : x₁ - x₂ ∈ p.asIdeal) (hu : x₂ ∉ p.asIdeal)
    (hb : (y₁ ∈ p.asIdeal ∧ y₂ + α * x₂ ∈ p.asIdeal) ∨
      (y₁ + α * x₁ ∈ p.asIdeal ∧ y₂ ∈ p.asIdeal)) :
    p ∈ suppliedReciprocalDomain d a c := by
  apply suppliedReciprocalDomain_mem d a c p hx
  have hx₁ : x₁ ∉ p.asIdeal := by
    intro h
    apply hu
    simpa only [sub_sub_cancel] using p.asIdeal.sub_mem h hx
  intro hy
  rcases hb with ⟨hb₁, hb₂⟩ | ⟨hb₁, hb₂⟩
  · have hy₂ : y₂ ∈ p.asIdeal := by
      simpa only [sub_sub_cancel] using p.asIdeal.sub_mem hb₁ hy
    have hm : α * x₂ ∈ p.asIdeal := by
      simpa only [add_sub_cancel_left] using p.asIdeal.sub_mem hb₂ hy₂
    exact hu ((p.asIdeal.unit_mul_mem_iff_mem (hα.map (algebraMap R S))).mp hm)
  · have hy₁ : y₁ ∈ p.asIdeal := by
      simpa only [sub_add_cancel] using p.asIdeal.add_mem hy hb₂
    have hm : α * x₁ ∈ p.asIdeal := by
      simpa only [add_sub_cancel_left] using p.asIdeal.sub_mem hb₁ hy₁
    exact hx₁ ((p.asIdeal.unit_mul_mem_iff_mem (hα.map (algebraMap R S))).mp hm)

end FLT.Mazur.WeierstrassDividedDepth
