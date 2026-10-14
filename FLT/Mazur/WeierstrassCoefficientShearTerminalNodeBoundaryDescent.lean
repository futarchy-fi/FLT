/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSuccessiveShearTerminalConicBranches
public import FLT.Mazur.WeierstrassConicZeroPunctureCover
public import FLT.Mazur.WeierstrassConicZeroProjectiveDescent
public import FLT.Mazur.ProjectiveLineScaledReciprocalGluing

/-!
# Descent on the full strict terminal node boundary

The two full node branches impose compatibility on both punctures of the original conic.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
open scoped LaurentPolynomial
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassSuccessiveX WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option quotPrecheck false
universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R) (π : R)
  (k : ℕ) (b3 b4 b6 : R) (S : Type u) [Field S] [Algebra R S] (r : S)
  (hs : algebraMap R S (π ^ k) = 0) (hp : algebraMap R S π = 0)
  (h3 : algebraMap R S b3 = 0) (h4 : algebraMap R S b4 = 0)
  (hr : r ^ 2 + algebraMap R S W.a₁ * r - algebraMap R S W.a₂ = 0)
  (h6 : algebraMap R S b6 = 0)
  (a : Sˣ) (ha : (a : S) = (rootShearCurve (W.map (algebraMap R S)) r).a₁)
local notation "U" => rootShearCurve (W.map (algebraMap R S)) r
local notation "c" => algebraMap R S b6
local notation "hu" => Eq.mp (congrArg IsUnit ha) (Units.isUnit a)
local notation "ψ" => tensorShearTerminalNodeConicMap W π k b3 b4 b6 S r
  hs hp h3 h4 hr h6 a ha
local notation "b" => Spec.map (CommRingCat.ofHom (AlgHom.toRingHom ψ))
local notation "inc" => PrincipalOpenTransport.inclusion (conicT (U).a₁ c)
variable {Y : Scheme.{u}} (f₁ f₂ : ProjectiveLine.scheme S ⟶ Y)
  (g : PolygonNodeBranches.node S ⟶ Y)
local notation "D" => conicZeroProjectiveDesc (U).a₁ c hu h6 f₁ f₂

/-- The two whole node restrictions force compatibility on the full original conic boundary. -/
theorem coefficientShearTerminalNodeBoundary_desc
    (h₁ : PolygonCyclicAtlas.secondBranch S ≫ g = ProjectiveLine.right S ≫ f₁)
    (h₂ : PolygonCyclicAtlas.firstBranch S ≫ g = ProjectiveLine.right S ≫ f₂) :
    inc ≫ D = b ≫ g := by
  apply conicZeroBoundary_hom_ext U c hu h6
  · rw [conicZeroBoundaryFirst_parameter_assoc,
      tensorShearTerminalConicFirst_spec_assoc]
    have H := conicZeroProjectiveDesc_first (U).a₁ c hu h6 f₁ f₂
    simp only [Category.assoc] at H
    rw [H, h₁]
    simpa only [Category.assoc] using congrArg (· ≫ f₁) (ProjectiveLine.overlap_condition S)
  · rw [conicZeroBoundarySecond_parameter_assoc,
      tensorShearTerminalConicSecond_spec_assoc]
    have H := conicZeroProjectiveDesc_second (U).a₁ c hu h6 f₁ f₂
    simp only [Category.assoc] at H
    rw [H, h₂]
    simpa only [Category.assoc] using congrArg (· ≫ f₂) (ProjectiveLine.overlap_condition S)

end FLT.Mazur.WeierstrassDividedDepth
