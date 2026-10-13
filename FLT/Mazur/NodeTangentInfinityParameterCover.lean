/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.NodeTangentNormalizationInfinity
public import FLT.Mazur.WeierstrassNodalInfinityShearOpen
public import FLT.Mazur.WeierstrassSplitInfinityParameterOpen
public import FLT.Mazur.ProjectiveLineEndpointCover
public import FLT.Mazur.BinaryOpenDescent

/-!
# The original nonsplit infinity parameter and full affine line cover the normalization

The shifted infinity open contains the actual point at infinity, and the full
left chart contains all remaining points. Targets of descent remain arbitrary.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur
open WeierstrassIntegralChart WeierstrassDividedDepth ProjectiveLine
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option quotPrecheck false
variable {F : Type} [Field F] (W : WeierstrassCurve F)
  [Fact (Irreducible (nodeTangentPolynomial W))]
  (h₃ : W.a₃ = 0) (h₄ : W.a₄ = 0) (h₆ : W.a₆ = 0)
local notation "Q" => AdjoinRoot (nodeTangentPolynomial W)
local notation "U" => W.map (algebraMap F Q)
local notation "V" => nodeTangentShear W
local notation "r" => AdjoinRoot.root (nodeTangentPolynomial W)
local notation "h3" => show (U).a₃ = 0 from by simp only [WeierstrassCurve.map_a₃, h₃, map_zero]
local notation "h4" => show (U).a₄ = 0 from by simp only [WeierstrassCurve.map_a₄, h₄, map_zero]
local notation "h6" => show (U).a₆ = 0 from by simp only [WeierstrassCurve.map_a₆, h₆, map_zero]
local notation "hr" => nodeTangentRoot_equation W
variable (a : (AdjoinRoot (nodeTangentPolynomial W))ˣ)
  (ha : (a : AdjoinRoot (nodeTangentPolynomial W)) = (nodeTangentShear W).a₁)
local notation "he" => rootShearCurve_eq_splitNodal U r a
  (ha.trans (nodeTangentShear_coefficients W).1) hr h3 h4 h6
local notation "P" => nodeTangentInfinityParameter W h₃ h₄ h₆ a ha

/-- The original shifted infinity parameter is an open immersion. -/
instance nodeTangentInfinityParameter_isOpenImmersion : IsOpenImmersion P := by
  unfold nodeTangentInfinityParameter
  infer_instance

/-- The original infinity section survives both the shear and the split parameter. -/
@[reassoc] theorem nodeTangentInfinityParameter_zero :
    Spec.map (CommRingCat.ofHom (chartInfinityEvaluation (S := Q) U).toRingHom) ≫
      P = infinity Q := by
  rw [nodeTangentInfinityParameter, ← Category.assoc, nodalInfinityShear_zero]
  exact splitEquationInfinityParameter_zero V a he

/-- The actual shifted infinity chart and full affine line cover every scheme point. -/
theorem nodeTangentInfinityParameter_cover (x : scheme Q) :
    x ∈ Set.range (left Q) ∨ x ∈ Set.range P := by
  rcases torus_or_endpoints Q x with ⟨z, rfl⟩ | ⟨z, rfl⟩ | ⟨z, rfl⟩
  · exact Or.inl ⟨overlapLeft Q z, rfl⟩
  · exact Or.inl ⟨chartZero Q z, rfl⟩
  · right
    refine ⟨Spec.map (CommRingCat.ofHom
      (chartInfinityEvaluation (S := Q) U).toRingHom) z, ?_⟩
    exact congrArg (fun f => f z) (nodeTangentInfinityParameter_zero W h₃ h₄ h₆ a ha)

/-- These complete original charts detect maps into every scheme. -/
theorem nodeTangentInfinityParameter_hom_ext {Y : Scheme} (f g : scheme Q ⟶ Y)
    (hl : left Q ≫ f = left Q ≫ g) (hi : P ≫ f = P ≫ g) : f = g :=
  BinaryOpenDescent.hom_ext (left Q) P
    (nodeTangentInfinityParameter_cover W h₃ h₄ h₆ a ha) f g hl hi

end FLT.Mazur
