/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDilatationTerminalSectionBranches

/-!
# Ordered tangent values of an actual integral section

The normalized node coordinates are the residues of the original vertical
coordinate and its other tangent factor. A unit horizontal coordinate places
the section on exactly one punctured branch, at any strict divided depth.
-/

@[expose] public noncomputable section
open IsLocalRing
namespace FLT.Mazur.WeierstrassDilatation
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} {depth : ℕ} (D : SplitNodeDepth W π depth)
  (k : ℕ) (hk0 : 0 < k) (hk : 2 * k ≤ depth) (b3 b4 b6 : R)
  (h3 : W.a₃ = π ^ k * b3) (h4 : W.a₄ = π ^ k * b4)
  (h6 : W.a₆ = (π ^ k) ^ 2 * b6) (hp : 2 * k < depth)
local notation "F" => ResidueField R
local notation "C" => Coordinate W (π ^ k) b3 b4 b6
local notation "e" => residuePolygonEquiv D k hk0 hk b3 b4 b6 h3 h4 h6 hp
local notation "g" => sectionNodeEvaluation D k hk0 hk b3 b4 b6 h3 h4 h6 hp
local notation "a" => residueTangentUnit D
local notation "x" => WeierstrassDilatation.x W (π ^ k) b3 b4 b6
local notation "y" => WeierstrassDilatation.y W (π ^ k) b3 b4 b6

/-- The first normalized branch value is the original divided vertical residue. -/
theorem sectionNodeEvaluation_x (f : C →ₐ[R] R) :
    g f PolygonNodeLocalization.x = residue R (f y) := by
  have h := normalizedSectionEvaluation_apply
    (sectionResidueEvaluation k b3 b4 b6 f) e (tensorY W (π ^ k) b3 b4 b6 F)
  rw [residuePolygonEquiv_y, sectionResidueEvaluation_y] at h
  exact h

/-- The second branch value retains the other original tangent factor. -/
theorem sectionNodeEvaluation_y (f : C →ₐ[R] R) :
    g f PolygonNodeLocalization.y = residue R (f y + W.a₁ * f x) := by
  have h := normalizedSectionEvaluation_apply
    (sectionResidueEvaluation k b3 b4 b6 f) e (tensorX W (π ^ k) b3 b4 b6 F)
  change g f (e (tensorX W (π ^ k) b3 b4 b6 F)) = _ at h
  rw [residuePolygonEquiv_x, map_mul, map_sub, AlgHom.commutes,
    Algebra.algebraMap_self_apply, sectionResidueEvaluation_x, sectionNodeEvaluation_x] at h
  have hh := congrArg (fun z : F => (a : F) * z) h
  rw [← mul_assoc, Units.mul_inv, one_mul, residueTangentUnit_val] at hh
  rw [map_add, map_mul]
  linear_combination hh

include D hk0 hk h3 h4 h6 hp in
/-- The actual two tangent residues have product zero. -/
theorem sectionNodeEvaluation_tangent_product (f : C →ₐ[R] R) :
    residue R (f y) * residue R (f y + W.a₁ * f x) = 0 := by
  rw [← sectionNodeEvaluation_x D k hk0 hk b3 b4 b6 h3 h4 h6 hp,
    ← sectionNodeEvaluation_y D k hk0 hk b3 b4 b6 h3 h4 h6 hp,
    ← map_mul, PolygonNodeLocalization.x_mul_y, map_zero]

/-- A horizontal unit forces one and only one nonzero tangent residue. -/
theorem sectionNodeEvaluation_horizontal_branches (f : C →ₐ[R] R) (hx : IsUnit (f x)) :
    (g f PolygonNodeLocalization.x = 0 ∧ g f PolygonNodeLocalization.y ≠ 0) ∨
      (g f PolygonNodeLocalization.x ≠ 0 ∧ g f PolygonNodeLocalization.y = 0) := by
  have hp0 : g f PolygonNodeLocalization.x * g f PolygonNodeLocalization.y = 0 := by
    rw [← map_mul, PolygonNodeLocalization.x_mul_y, map_zero]
  have hn : g f PolygonNodeLocalization.x ≠ g f PolygonNodeLocalization.y := by
    intro he
    have h := normalizedSectionEvaluation_apply
      (sectionResidueEvaluation k b3 b4 b6 f) e (tensorX W (π ^ k) b3 b4 b6 F)
    change g f (e (tensorX W (π ^ k) b3 b4 b6 F)) = _ at h
    rw [residuePolygonEquiv_x, map_mul, map_sub, he, sub_self, mul_zero,
      sectionResidueEvaluation_x] at h
    exact (hx.map (residue R)).ne_zero h.symm
  rcases mul_eq_zero.mp hp0 with hx0 | hy0
  · exact Or.inl ⟨hx0, fun hy0 => hn (hx0.trans hy0.symm)⟩
  · exact Or.inr ⟨fun hx0 => hn (hx0.trans hy0.symm), hy0⟩

end FLT.Mazur.WeierstrassDilatation
