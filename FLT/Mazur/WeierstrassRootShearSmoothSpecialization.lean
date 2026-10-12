/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassRootShearParameterCoefficient
public import FLT.Mazur.WeierstrassSmoothCoefficientSpecialization
public import FLT.Mazur.WeierstrassProjectiveCoefficientSquare
public import FLT.Mazur.ProjectiveCoefficientFunctor

/-!
# Specializing the actual ordered root parameter of the full smooth cubic

The coefficient map on Laurent rings is the full smooth specialization in
both original root charts. No restriction excludes the torus identity.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
open scoped LaurentPolynomial
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option quotPrecheck false
variable {R S T : Type} [CommRing R] [CommRing S] [CommRing T]
  [Algebra R S] [Algebra R T] (W : WeierstrassCurve R) (f : S →ₐ[R] T)
  (r : S) (a : Sˣ) (b : Tˣ) (hab : Units.map f.toRingHom a = b)
local notation "V" => W.map (algebraMap R S)
local notation "U" => W.map (algebraMap R T)
variable (ha : (a : S) = (W.map (algebraMap R S)).a₁ + 2 * r)
  (hr : r ^ 2 + (W.map (algebraMap R S)).a₁ * r - (W.map (algebraMap R S)).a₂ = 0)
  (h3 : (W.map (algebraMap R S)).a₃ = 0)
  (h4 : (W.map (algebraMap R S)).a₄ = 0) (h6 : (W.map (algebraMap R S)).a₆ = 0)
  (hb : (b : T) = (W.map (algebraMap R T)).a₁ + 2 * f r)
  (hv : (f r) ^ 2 + (W.map (algebraMap R T)).a₁ * f r -
    (W.map (algebraMap R T)).a₂ = 0)
  (g3 : (W.map (algebraMap R T)).a₃ = 0)
  (g4 : (W.map (algebraMap R T)).a₄ = 0) (g6 : (W.map (algebraMap R T)).a₆ = 0)
local notation "IS" => rootShearTorusSmoothIso V r a ha hr h3 h4 h6
local notation "IT" => rootShearTorusSmoothIso U (f r) b
  hb hv g3 g4 g6
local notation "L" => Spec.map (CommRingCat.ofHom (nodalLaurentCoefficientMap f.toRingHom))

include hab ha hr h3 h4 h6 hb hv g3 g4 g6 in
/-- The actual root parameter specializes with its Laurent character unchanged. -/
@[reassoc] theorem rootShearTorusSmoothIso_specialization :
    (IT).hom ≫ originalSmoothSpecialization W f = L ≫ (IS).hom := by
  symm
  apply originalSmoothSpecialization_unique
  · apply (cancel_mono (integralSmoothOpen W).ι).mp
    apply (cancel_mono (integralProjectiveMap W)).mp
    simp only [Category.assoc, originalSmoothCoefficientMap_inclusion,
      integralProjectiveMap_coefficient]
    rw [rootShearTorusSmoothIso_projectiveCoefficient_assoc f.toRingHom V U r a b hab
      ha hr h3 h4 h6 hb hv g3 g4 g6]
    rw [ProjectiveSpace.coefficientMap_comp]
    have hf : f.toRingHom.comp (algebraMap R S) = algebraMap R T :=
      RingHom.ext f.commutes
    rw [hf]
    rfl
  · rw [Category.assoc, rootShearTorusSmoothIso_structure,
      nodalLaurentCoefficientMap_structure]
    exact (rootShearTorusSmoothIso_structure_assoc U (f r) b hb hv g3 g4 g6 _).symm

include hab ha hr h3 h4 h6 hb hv g3 g4 g6 in
/-- Conjugating full smooth specialization by the two actual parameters is coefficient change. -/
theorem rootShearTorusParameter_specialization :
    (IT).hom ≫ originalSmoothSpecialization W f ≫ (IS).inv = L := by
  rw [rootShearTorusSmoothIso_specialization_assoc W f r a b hab
    ha hr h3 h4 h6 hb hv g3 g4 g6, Iso.hom_inv_id, Category.comp_id]

end FLT.Mazur.WeierstrassDividedDepth
