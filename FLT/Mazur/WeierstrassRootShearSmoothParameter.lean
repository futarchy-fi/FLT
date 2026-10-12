/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassVariableChangeSmoothIso
public import FLT.Mazur.WeierstrassDividedShearData
public import FLT.Mazur.WeierstrassSplitNodalRelativeSmooth

/-!
# The ordered torus parameter on the original root-split smooth curve

The full smooth scheme of the original nodal equation is the Laurent torus
via the actual tangent-root shear. The comparison retains the original cubic
map and base morphism. Compatibility of group laws is a separate assertion.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory WeierstrassCurve
open scoped LaurentPolynomial
namespace FLT.Mazur.WeierstrassIntegralChart
open WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R] (W : WeierstrassCurve R) (r : R) (a : Rˣ)
  (ha : (a : R) = W.a₁ + 2 * r)
  (hr : r ^ 2 + W.a₁ * r - W.a₂ = 0)
  (h3 : W.a₃ = 0) (h4 : W.a₄ = 0) (h6 : W.a₆ = 0)
local notation "C" => (VariableChange.mk 1 0 r 0 : VariableChange R)

include ha hr h3 h4 h6

/-- The chosen root makes the entire original equation exactly the split nodal equation. -/
theorem rootShearCurve_eq_splitNodal : rootShearCurve W r = splitNodalEquation a := by
  obtain ⟨g1, g2, g3, g4, g6⟩ := rootShearCurve_coefficients (W := W) r
  ext
  · exact g1.trans ha.symm
  · change (rootShearCurve W r).a₂ = 0
    rw [g2]
    linear_combination -hr
  · exact g3.trans h3
  · change (rootShearCurve W r).a₄ = 0
    rw [g4, h4, h3, mul_zero, sub_zero]
  · exact g6.trans h6

local notation "he" => rootShearCurve_eq_splitNodal W r a ha hr h3 h4 h6
local notation "E" => integralVariableChangeIso W (splitNodalEquation a) C he
local notation "J" => integralVariableChangeSmoothIso W (splitNodalEquation a) C he

/-- The whole original smooth curve is the torus with the actual ordered tangent parameter. -/
def rootShearTorusSmoothIso : Spec (.of R[T;T⁻¹]) ≅ (integralSmoothOpen W).toScheme :=
  splitNodalRelativeSmoothIso a ≪≫ J

/-- Every original cubic function is retained through the actual root-shear isomorphism. -/
@[reassoc] theorem rootShearTorusSmoothIso_inclusion :
    (rootShearTorusSmoothIso W r a ha hr h3 h4 h6).hom ≫ (integralSmoothOpen W).ι =
      splitNodalTorusToCurve a ≫ (E).hom := by
  change (splitNodalTorusToSmooth a ≫ integralVariableChangeSmoothMap W
    (splitNodalEquation a) C he) ≫ _ = _
  rw [Category.assoc, integralVariableChangeSmoothMap_inclusion,
    splitNodalTorusToSmooth_inclusion_assoc]

/-- The original smooth parameter comparison preserves the whole coefficient structure. -/
@[reassoc] theorem rootShearTorusSmoothIso_structure :
    (rootShearTorusSmoothIso W r a ha hr h3 h4 h6).hom ≫ integralSmoothStructure W =
      (MultiplicativeGroupScheme.gm R).hom := by
  change ((splitNodalRelativeSmoothIso a).hom ≫
    integralVariableChangeSmoothMap W (splitNodalEquation a) C he) ≫ _ = _
  rw [Category.assoc, integralVariableChangeSmoothMap_structure,
    splitNodalRelativeSmoothIso_structure]

/-- The actual original smooth parameter and torus are isomorphic over the coefficient base. -/
def rootShearTorusSmoothOverIso : MultiplicativeGroupScheme.gm R ≅
    Over.mk (integralSmoothStructure W) :=
  Over.isoMk (rootShearTorusSmoothIso W r a ha hr h3 h4 h6)
    (rootShearTorusSmoothIso_structure W r a ha hr h3 h4 h6)

end FLT.Mazur.WeierstrassIntegralChart
