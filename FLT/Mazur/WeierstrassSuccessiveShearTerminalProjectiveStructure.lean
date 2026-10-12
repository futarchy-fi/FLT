/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSuccessiveShearTerminalProjectiveIso
public import FLT.Mazur.WeierstrassSuccessiveShearTerminalAffineStructure
public import FLT.Mazur.ProjectiveLineStandardComparison
public import FLT.Mazur.ProjectiveSpaceProper

/-!
# Properness of the original terminal component over the coefficient field

The projective-line comparison respects the original coefficient morphism.
It therefore identifies the original component with the standard projective
line over that field and proves its structure morphism proper.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
open scoped Polynomial LaurentPolynomial
namespace FLT.Mazur.WeierstrassSuccessiveShearTerminal
open WeierstrassModificationX WeierstrassSuccessiveX WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option quotPrecheck false
universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R) (π : R)
  (k : ℕ) (b3 b4 b6 : R) (S : Type u) [Field S] [Algebra R S] (ρ : S)
  (hs : algebraMap R S (π ^ k) = 0) (hp : algebraMap R S π = 0)
  (h3 : algebraMap R S b3 = 0) (h4 : algebraMap R S b4 = 0)
  (hr : ρ ^ 2 + algebraMap R S W.a₁ * ρ - algebraMap R S W.a₂ = 0)
  (hc : IsUnit (algebraMap R S b6)) (u : Sˣ)
  (hu : (u : S) = (rootShearCurve (W.map (algebraMap R S)) ρ).a₁)
local notation "U" => rootShearCurve (W.map (algebraMap R S)) ρ
local notation "K" => S
local notation "a" => WeierstrassCurve.a₁ U
local notation "c" => algebraMap R S b6
local notation "ha" => Eq.mp (congrArg IsUnit hu) (Units.isUnit u)
local notation "P" => laurentConicComponent W π k b3 b4 b6 S ρ hs hp h3 h4 hr hc u hu
local notation "l" => laurentConicComponentConic W π k b3 b4 b6 S ρ hs hp h3 h4 hr hc u hu
local notation "r" => laurentConicComponentTorus W π k b3 b4 b6 S ρ hs hp h3 h4 hr hc u hu
local notation "j" => PrincipalOpenTransport.inclusion (conicParameterPolynomial c)
local notation "f" => laurentConicComponentFirstAffine W π k b3 b4 b6 S ρ hs hp h3 h4 hr hc u hu
local notation "g" => laurentConicComponentSecondAffine W π k b3 b4 b6 S ρ hs hp h3 h4 hr hc u hu

local notation "E" => ProjectiveLine.chartScalingIso K (Inv.inv (IsUnit.unit hc))

local notation "p" => laurentConicComponentStructure W π k b3 b4 b6 S ρ hs hp h3 h4 hr hc u hu
local notation "J" => laurentConicComponentProjectiveIso W π k b3 b4 b6 S ρ hs hp h3 h4 hr hc u hu

/-- The projective comparison retains the coefficient structure. -/
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
  rw [← laurentConicComponentProjectiveIso_structure W π k b3 b4 b6 S ρ hs hp h3 h4 hr hc u hu,
    Iso.inv_hom_id_assoc]

/-- The actual glued component is the projective line as a scheme over the coefficient field. -/
def laurentConicComponentProjectiveOverIso :
    Over.mk (ProjectiveLine.toBase K) ≅ Over.mk p :=
  Over.isoMk J (laurentConicComponentProjectiveIso_structure W π k b3 b4 b6 S ρ hs hp h3 h4 hr
    hc u hu)

/-- The full original component is proper over its original coefficient field. -/
instance laurentConicComponentStructure_proper : IsProper p := by
  rw [← laurentConicComponentProjectiveIso_inv_structure W π k b3 b4 b6 S ρ hs hp h3 h4 hr hc u hu,
    ← ProjectiveLine.standardIso_toBase]
  infer_instance

end FLT.Mazur.WeierstrassSuccessiveShearTerminal
