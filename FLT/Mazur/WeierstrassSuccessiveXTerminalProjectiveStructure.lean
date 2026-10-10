/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSuccessiveXTerminalProjectiveIso
public import FLT.Mazur.WeierstrassSuccessiveXTerminalAffineStructure
public import FLT.Mazur.ProjectiveLineStandardComparison
public import FLT.Mazur.ProjectiveSpaceProper

/-!
# Properness of the original terminal component over the residue field

The projective-line comparison respects the original coefficient morphism.
It therefore identifies the original component with the standard projective
line over that field and proves its structure morphism proper.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
open scoped Polynomial LaurentPolynomial
namespace FLT.Mazur.WeierstrassSuccessiveX
open WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} {n : ℕ} (D : SplitNodeDepth W π n)
  (k : ℕ) (hk : 2 * (k + 1) ≤ n) (b3 b4 b6 : R)
  (h3 : W.a₃ = π ^ (k + 1) * b3) (h4 : W.a₄ = π ^ (k + 1) * b4)
  (h6 : W.a₆ = (π ^ (k + 1)) ^ 2 * b6) (hp : 2 * (k + 1) = n)
local notation "K" => ResidueField R
local notation "a" => WeierstrassCurve.a₁ (W.map (residue R))
local notation "c" => residue R b6
local notation "ha" => D.a₁_unit.map (residue R)
local notation "hc" => laurentConicComponent_constant_isUnit D k b6 h6 hp
local notation "P" => laurentConicComponent D k hk b3 b4 b6 h3 h4 h6 hp
local notation "l" => laurentConicComponentConic D k hk b3 b4 b6 h3 h4 h6 hp
local notation "r" => laurentConicComponentTorus D k hk b3 b4 b6 h3 h4 h6 hp
local notation "j" => PrincipalOpenTransport.inclusion (conicParameterPolynomial c)
local notation "f" => laurentConicComponentFirstAffine D k hk b3 b4 b6 h3 h4 h6 hp
local notation "g" => laurentConicComponentSecondAffine D k hk b3 b4 b6 h3 h4 h6 hp

local notation "E" => ProjectiveLine.chartScalingIso K (Inv.inv (IsUnit.unit hc))

local notation "p" => laurentConicComponentStructure D k hk b3 b4 b6 h3 h4 h6 hp
local notation "J" => laurentConicComponentProjectiveIso D k hk b3 b4 b6 h3 h4 h6 hp

/-- The projective comparison retains the original residue-field coefficient structure. -/
@[reassoc] theorem laurentConicComponentProjectiveIso_structure :
    (J).hom ≫ p = ProjectiveLine.toBase K := by
  apply pushout.hom_ext
  · change ProjectiveLine.left K ≫ _ = ProjectiveLine.left K ≫ _
    rw [laurentConicComponentProjectiveIso_left_assoc,
      laurentConicComponentFirstAffine_structure, ProjectiveLine.left_toBase]
    exact ProjectiveLine.chartScaling_toBase K _
  · change ProjectiveLine.right K ≫ _ = ProjectiveLine.right K ≫ _
    rw [laurentConicComponentProjectiveIso_right_assoc,
      laurentConicComponentSecondAffine_structure, ProjectiveLine.right_toBase]

/-- The inverse comparison is also over the original field. -/
@[reassoc] theorem laurentConicComponentProjectiveIso_inv_structure :
    (J).inv ≫ ProjectiveLine.toBase K = p := by
  rw [← laurentConicComponentProjectiveIso_structure D k hk b3 b4 b6 h3 h4 h6 hp,
    Iso.inv_hom_id_assoc]

/-- The actual glued component is the projective line as a scheme over the residue field. -/
def laurentConicComponentProjectiveOverIso :
    Over.mk (ProjectiveLine.toBase K) ≅ Over.mk p :=
  Over.isoMk J (laurentConicComponentProjectiveIso_structure D k hk b3 b4 b6 h3 h4 h6 hp)

/-- The full original component is proper over its original coefficient field. -/
instance laurentConicComponentStructure_proper : IsProper p := by
  rw [← laurentConicComponentProjectiveIso_inv_structure D k hk b3 b4 b6 h3 h4 h6 hp,
    ← ProjectiveLine.standardIso_toBase]
  infer_instance

end FLT.Mazur.WeierstrassSuccessiveX
