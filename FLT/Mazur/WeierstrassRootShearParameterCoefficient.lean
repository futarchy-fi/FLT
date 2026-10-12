/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSplitNodalProjectiveCoefficient
public import FLT.Mazur.WeierstrassRootShearSmoothParameter
public import FLT.Mazur.WeierstrassVariableChangeCoefficient

/-!
# The actual root-sheared torus parameter respects coefficient maps

The independently constructed proper variable changes agree after mapping
the tangent root and tangent unit. The comparison retains the full original
projective cubic map.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory WeierstrassCurve
open scoped LaurentPolynomial
namespace FLT.Mazur.WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option quotPrecheck false
variable {S T : Type} [CommRing S] [CommRing T] (f : S →+* T)
  (W : WeierstrassCurve S) (V : WeierstrassCurve T) (r : S) (a : Sˣ)
  (b : Tˣ) (hab : Units.map f a = b)
  (ha : (a : S) = W.a₁ + 2 * r)
  (hr : r ^ 2 + W.a₁ * r - W.a₂ = 0)
  (h3 : W.a₃ = 0) (h4 : W.a₄ = 0) (h6 : W.a₆ = 0)
  (hb : (b : T) = V.a₁ + 2 * f r)
  (hv : (f r) ^ 2 + V.a₁ * f r - V.a₂ = 0)
  (g3 : V.a₃ = 0) (g4 : V.a₄ = 0) (g6 : V.a₆ = 0)
local notation "IS" => rootShearTorusSmoothIso W r a ha hr h3 h4 h6
local notation "IT" => rootShearTorusSmoothIso V (f r) b hb hv g3 g4 g6
local notation "L" => Spec.map (CommRingCat.ofHom (nodalLaurentCoefficientMap f))
local notation "C" => (VariableChange.mk 1 0 r 0 : VariableChange S)
local notation "D" => (VariableChange.mk 1 0 (f r) 0 : VariableChange T)

/-- Mapping the chosen root gives exactly the specialized proper shear. -/
theorem rootShearVariableChange_coefficient : (C).map f = D := by
  ext <;> simp [VariableChange.map]

include hab in
/-- Both full torus parameters retain the same original projective cubic functions. -/
@[reassoc] theorem rootShearTorusSmoothIso_projectiveCoefficient :
    L ≫ (IS).hom ≫ (integralSmoothOpen W).ι ≫ integralProjectiveMap W =
      (IT).hom ≫ (integralSmoothOpen V).ι ≫ integralProjectiveMap V ≫
        ProjectiveSpace.coefficientMap f (Fin 3) := by
  rw [rootShearTorusSmoothIso_inclusion_assoc,
    rootShearTorusSmoothIso_inclusion_assoc]
  change L ≫ splitNodalTorusToCurve a ≫ integralVariableChangeTo W _ C _ ≫ _ =
    splitNodalTorusToCurve b ≫ integralVariableChangeTo V _ D _ ≫ _
  rw [integralVariableChangeTo_projectiveMap,
    integralVariableChangeTo_projectiveMap_assoc]
  rw [splitNodalTorus_projectiveCoefficient_assoc f a b hab,
    WeierstrassVariableChangeLinear.projectiveIso_coefficient,
    rootShearVariableChange_coefficient]

end FLT.Mazur.WeierstrassIntegralChart
