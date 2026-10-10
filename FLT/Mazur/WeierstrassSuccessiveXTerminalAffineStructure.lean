/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSuccessiveXTerminalAffineCover

/-!
# Coefficient structures on both completed terminal affine charts

The full charts retain the residue-field structure of the original conic
and of the entire Laurent chart, including their complete parameter opens.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
open scoped Polynomial LaurentPolynomial
namespace FLT.Mazur.WeierstrassSuccessiveX
open WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
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

local notation "p" => laurentConicComponentStructure D k hk b3 b4 b6 h3 h4 h6 hp
local notation "q₁" => laurentConicComponentFirstParameter D k hk b3 b4 b6 h3 h4 h6 hp
local notation "q₂" => laurentConicComponentSecondParameter D k hk b3 b4 b6 h3 h4 h6 hp
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

/-- The completed first affine chart is over the original residue field. -/
@[reassoc] theorem laurentConicComponentFirstAffine_structure :
    f ≫ p = ProjectiveLine.chartToBase K := by
  apply (cancel_epi (terminalFirstAffineIso D k hk b3 b4 b6 h3 h4 h6 hp).hom).mp
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

/-- The completed second affine chart is over the same residue field. -/
@[reassoc] theorem laurentConicComponentSecondAffine_structure :
    g ≫ p = ProjectiveLine.chartToBase K := by
  apply (cancel_epi (terminalSecondAffineIso D k hk b3 b4 b6 h3 h4 h6 hp).hom).mp
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

end FLT.Mazur.WeierstrassSuccessiveX
