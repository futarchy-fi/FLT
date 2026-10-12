/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSuccessiveShearTerminalAffineCover

/-!
# Coefficient structures on both completed terminal affine charts

The full charts retain the residue-field structure of the original conic
and of the entire Laurent chart, including their complete parameter opens.
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
/-- The standard torus inclusion preserves the original coefficient morphism. -/
theorem terminalAffineTorus_structure (L : Type u) [Field L] :
    ProjectiveLine.overlapLeft L ≫ ProjectiveLine.chartToBase L =
      (MultiplicativeGroupScheme.gm L).hom := by
  change Spec.map (CommRingCat.ofHom Polynomial.toLaurent) ≫
    Spec.map (CommRingCat.ofHom Polynomial.C) =
      Spec.map (CommRingCat.ofHom (algebraMap L L[T;T⁻¹]))
  rw [← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro x
  exact Polynomial.toLaurent_C x

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

local notation "p" => laurentConicComponentStructure W π k b3 b4 b6 S ρ hs hp h3 h4 hr hc u hu
local notation "q₁" => laurentConicComponentFirstParameter W π k b3 b4 b6 S ρ hs hp h3 h4 hr hc u hu
local notation "q₂" => laurentConicComponentSecondParameter W π k b3 b4 b6 S ρ hs hp h3 h4 hr hc
  u hu
local notation "B" => Spec.map (CommRingCat.ofHom (algebraMap K (ConicParameterOpen c)))

/-- The original first full parameter neighborhood preserves every coefficient. -/
@[reassoc] theorem laurentConicComponentFirstParameter_structure : q₁ ≫ p = B := by
  simp only [laurentConicComponentFirstParameter, Category.assoc,
    laurentConicComponentConic_structure]
  erw [WeierstrassDividedDepth.terminalComponent_algebra_structure
    (Algebra.algHom K (ConicCoordinate a c) (ConicFirstOpen a c)),
    WeierstrassDividedDepth.terminalComponent_algebra_structure
      (conicFirstParameterEquiv a c ha).symm.toAlgHom]

/-- The original second full parameter neighborhood preserves every coefficient. -/
@[reassoc] theorem laurentConicComponentSecondParameter_structure : q₂ ≫ p = B := by
  simp only [laurentConicComponentSecondParameter, Category.assoc,
    laurentConicComponentConic_structure]
  erw [WeierstrassDividedDepth.terminalComponent_algebra_structure
    (Algebra.algHom K (ConicCoordinate a c) (ConicSecondOpen a c)),
    WeierstrassDividedDepth.terminalComponent_algebra_structure
      (conicSecondParameterEquiv a c ha).symm.toAlgHom]

/-- The completed first affine chart is over the coefficient field. -/
@[reassoc] theorem laurentConicComponentFirstAffine_structure :
    f ≫ p = ProjectiveLine.chartToBase K := by
  apply (cancel_epi (terminalFirstAffineIso W π k b3 b4 b6 S ρ hs hp h3 h4 hr hc u hu).hom).mp
  apply pushout.hom_ext
  · simp only [terminalFirstAffineIso_parameter_assoc,
      laurentConicComponentFirstAffine_parameter_assoc,
      laurentConicComponentFirstParameter_structure]
    exact (WeierstrassDividedDepth.terminalComponent_algebra_structure
      (Algebra.algHom K K[X] (ConicParameterOpen c))).symm
  · simp only [terminalFirstAffineIso_torus_assoc, laurentConicComponentFirstAffine_torus_assoc,
      laurentConicComponentTorus_structure]
    rw [ProjectiveLine.scaledOverlapLeft, Category.assoc]
    change _ = ProjectiveLine.overlapLeft K ≫
      ProjectiveLine.chartScaling K ((hc).unit)⁻¹ ≫ ProjectiveLine.chartToBase K
    rw [ProjectiveLine.chartScaling_toBase]
    exact (terminalAffineTorus_structure K).symm

/-- The completed second affine chart is over the same coefficient field. -/
@[reassoc] theorem laurentConicComponentSecondAffine_structure :
    g ≫ p = ProjectiveLine.chartToBase K := by
  apply (cancel_epi (terminalSecondAffineIso W π k b3 b4 b6 S ρ hs hp h3 h4 hr hc u hu).hom).mp
  apply pushout.hom_ext
  · simp only [terminalSecondAffineIso_parameter_assoc,
      laurentConicComponentSecondAffine_parameter_assoc,
      laurentConicComponentSecondParameter_structure]
    exact (WeierstrassDividedDepth.terminalComponent_algebra_structure
      (Algebra.algHom K K[X] (ConicParameterOpen c))).symm
  · simp only [terminalSecondAffineIso_torus_assoc, laurentConicComponentSecondAffine_torus_assoc,
      laurentConicComponentTorus_structure]
    rw [← ProjectiveLine.overlap_toBase]
    exact (terminalAffineTorus_structure K).symm

end FLT.Mazur.WeierstrassSuccessiveShearTerminal
