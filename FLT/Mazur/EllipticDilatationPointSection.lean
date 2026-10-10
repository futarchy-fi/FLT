/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDilatationMorphism
public import FLT.Mazur.EllipticNodePointCoordinates
public import FLT.Mazur.EllipticIntegralPointSection

/-!
# Original nodal points lift to the actual divided affine chart

Primitive nodal coordinates define a section of the flat divided chart.
Its contraction is the canonical integral section of precisely the original
generic point. The generic point is not reassigned to an unrelated model.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory WeierstrassCurve

namespace FLT.Mazur.WeierstrassDilatation

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
variable {K : Type u} [Field K] (A : ValuationSubring K) (W : WeierstrassCurve A)
  {π : A} (hπ : π ≠ 0) {P : (W.map (algebraMap A K)).toProjective.Point}
  (v : NodePointCoordinates A W π P) (b3 b4 b6 : A)
  (h3 : W.a₃ = π ^ v.depth * b3) (h4 : W.a₄ = π ^ v.depth * b4)
  (h6 : W.a₆ = (π ^ v.depth) ^ 2 * b6)

/-- The integral affine representative is an actual normalized projective solution. -/
theorem nodePoint_projective_equation :
    (W.map (algebraMap A A)).toProjective.Equation
      ![π ^ v.depth * v.a, π ^ v.depth * v.b, 1] := by
  have h := (Affine.equation_iff _ _).mp v.equation
  rw [Projective.equation_iff]
  simp only [Algebra.algebraMap_self, WeierstrassCurve.map_id, Projective.fin3_def_ext]
  linear_combination h

include hπ h3 h4 h6 in
/-- The primitive nodal coordinates solve the actual divided chart equation. -/
theorem nodePoint_divided_equation :
    v.b ^ 2 + (algebraMap A A W.a₁ * v.a + algebraMap A A b3) * v.b =
      algebraMap A A (π ^ v.depth) * v.a ^ 3 + algebraMap A A W.a₂ * v.a ^ 2 +
        algebraMap A A b4 * v.a + algebraMap A A b6 := by
  apply equation_of_scaled W (π ^ v.depth) b3 b4 b6 h3 h4 h6
    (isRegular_iff_ne_zero.mpr (pow_ne_zero v.depth hπ))
  exact nodePoint_projective_equation A W v

/-- Evaluation at the original primitive nodal coordinates. -/
def nodePointEvaluation : Coordinate W (π ^ v.depth) b3 b4 b6 →ₐ[A] A :=
  evaluation W (π ^ v.depth) b3 b4 b6 v.a v.b
    (nodePoint_divided_equation A W hπ v b3 b4 b6 h3 h4 h6)

/-- The original point defines a genuine section of the divided chart. -/
def nodePointSection : Spec (.of A) ⟶ Spec (.of (Coordinate W (π ^ v.depth) b3 b4 b6)) :=
  Spec.map (CommRingCat.ofHom (nodePointEvaluation A W hπ v b3 b4 b6 h3 h4 h6).toRingHom)

/-- The normalized chart still represents the exact original projective point. -/
theorem nodePoint_projective_represents :
    (⟦fun i => ((![(π ^ v.depth * v.a), (π ^ v.depth * v.b), 1] i : A) : K)⟧ :
        Projective.PointClass K) = P.point := by
  rw [congrArg Projective.Point.point v.represents]
  apply congrArg Quotient.mk''
  ext i
  fin_cases i <;> simp

/-- Contraction of the divided section is the canonical section of the original point. -/
@[reassoc] theorem nodePointSection_toCurve :
    nodePointSection A W hπ v b3 b4 b6 h3 h4 h6 ≫
        toCurve W (π ^ v.depth) b3 b4 b6 h3 h4 h6 =
      WeierstrassIntegralChart.integralPointSection A W P := by
  change Spec.map (CommRingCat.ofHom (evaluation W (π ^ v.depth) b3 b4 b6 v.a v.b
    (nodePoint_divided_equation A W hπ v b3 b4 b6 h3 h4 h6)).toRingHom) ≫ _ = _
  rw [evaluation_toCurve W (π ^ v.depth) b3 b4 b6 h3 h4 h6 v.a v.b
    (nodePoint_divided_equation A W hπ v b3 b4 b6 h3 h4 h6)
    (nodePoint_projective_equation A W v)]
  exact (WeierstrassIntegralChart.integralPointSection_chart A W P 2 _
    (nodePoint_projective_equation A W v) rfl (nodePoint_projective_represents A W v)).symm

/-- The constructed divided-chart morphism is a section over the original valuation ring. -/
@[reassoc] theorem nodePointSection_structure :
    nodePointSection A W hπ v b3 b4 b6 h3 h4 h6 ≫
        Spec.map (CommRingCat.ofHom
          (algebraMap A (Coordinate W (π ^ v.depth) b3 b4 b6))) = 𝟙 _ := by
  rw [← toCurve_structure W (π ^ v.depth) b3 b4 b6 h3 h4 h6,
    ← Category.assoc, nodePointSection_toCurve,
    WeierstrassIntegralChart.integralPointSection_structure]

/-- Generic restriction after contraction is the original classical scheme point. -/
theorem nodePointSection_generic :
    Spec.map (CommRingCat.ofHom (algebraMap A K)) ≫
        nodePointSection A W hπ v b3 b4 b6 h3 h4 h6 ≫
          toCurve W (π ^ v.depth) b3 b4 b6 h3 h4 h6 =
      (WeierstrassIntegralChart.projectiveToIntegral W P).left := by
  rw [nodePointSection_toCurve, WeierstrassIntegralChart.integralPointSection_generic]

end FLT.Mazur.WeierstrassDilatation
