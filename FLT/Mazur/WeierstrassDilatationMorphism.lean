/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDilatationAlgebra
public import FLT.Mazur.WeierstrassProjectivePointNaturality

/-!
# The divided affine chart maps to the original Weierstrass cubic

The coordinate substitution (u,v) ↦ (s u,s v) defines an actual morphism over
the original base. The equation is proved in the flat chart algebra. No
identification with a resolved global model is assumed.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory WeierstrassCurve

namespace FLT.Mazur.WeierstrassDilatation

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R) (s b3 b4 b6 : R)
  (h3 : W.a₃ = s * b3) (h4 : W.a₄ = s * b4) (h6 : W.a₆ = s ^ 2 * b6)

include h3 h4 h6 in
/-- The scaled universal coordinates satisfy the original homogeneous cubic. -/
theorem scaled_equation :
    (W.map (algebraMap R (Coordinate W s b3 b4 b6))).toProjective.Equation
      ![algebraMap R _ s * x W s b3 b4 b6,
        algebraMap R _ s * y W s b3 b4 b6, 1] := by
  have h := equation W s b3 b4 b6
  rw [Projective.equation_iff]
  simp only [Projective.fin3_def_ext, map_a₁, map_a₂, map_a₃, map_a₄, map_a₆,
    h3, h4, h6, map_mul, map_pow]
  linear_combination (algebraMap R (Coordinate W s b3 b4 b6) s) ^ 2 * h

include h3 h4 h6 in
/-- Regularity of the scale recovers the divided equation from an actual scaled point. -/
theorem equation_of_scaled {S : Type u} [CommRing S] [Algebra R S]
    (hs : IsRegular (algebraMap R S s)) (u v : S)
    (h : (W.map (algebraMap R S)).toProjective.Equation
      ![algebraMap R S s * u, algebraMap R S s * v, 1]) :
    v ^ 2 + (algebraMap R S W.a₁ * u + algebraMap R S b3) * v =
      algebraMap R S s * u ^ 3 + algebraMap R S W.a₂ * u ^ 2 +
        algebraMap R S b4 * u + algebraMap R S b6 := by
  apply (IsRegular.pow 2 hs).left
  rw [Projective.equation_iff] at h
  simp only [Projective.fin3_def_ext, map_a₁, map_a₂, map_a₃, map_a₄, map_a₆,
    h3, h4, h6, map_mul, map_pow] at h
  linear_combination h

/-- The coordinate map from the original affine chart to its divided chart. -/
def fromOriginal : WeierstrassIntegralChart.Coordinate W 2 →ₐ[R] Coordinate W s b3 b4 b6 :=
  WeierstrassIntegralChart.evaluation W 2
    ![algebraMap R _ s * x W s b3 b4 b6, algebraMap R _ s * y W s b3 b4 b6, 1]
    (scaled_equation W s b3 b4 b6 h3 h4 h6) rfl

/-- The first original coordinate is the scaling parameter times the divided coordinate. -/
@[simp] theorem fromOriginal_x :
    fromOriginal W s b3 b4 b6 h3 h4 h6 (WeierstrassIntegralChart.coord W 2 0) =
      algebraMap R _ s * x W s b3 b4 b6 :=
  WeierstrassIntegralChart.evaluation_coord W 2 _ _ _ 0

/-- The second original coordinate is the scaling parameter times the divided coordinate. -/
@[simp] theorem fromOriginal_y :
    fromOriginal W s b3 b4 b6 h3 h4 h6 (WeierstrassIntegralChart.coord W 2 1) =
      algebraMap R _ s * y W s b3 b4 b6 :=
  WeierstrassIntegralChart.evaluation_coord W 2 _ _ _ 1

/-- The actual scheme morphism from the flat divided chart into the original cubic. -/
def toCurve : Spec (.of (Coordinate W s b3 b4 b6)) ⟶
    WeierstrassIntegralChart.integralCurve W :=
  Spec.map (CommRingCat.ofHom (fromOriginal W s b3 b4 b6 h3 h4 h6).toRingHom) ≫
    WeierstrassIntegralChart.integralCurveChart W 2

/-- This morphism lies over the original coefficient spectrum. -/
@[reassoc] theorem toCurve_structure :
    toCurve W s b3 b4 b6 h3 h4 h6 ≫ WeierstrassIntegralChart.integralCurveStructure W =
      Spec.map (CommRingCat.ofHom (algebraMap R (Coordinate W s b3 b4 b6))) :=
  WeierstrassIntegralChart.integralChartPoint_structure W 2 _ _ _

/-- An actual solution in any base algebra gives the prescribed point of the original cubic. -/
theorem evaluation_toCurve {S : Type u} [CommRing S] [Algebra R S] (u v : S)
    (h : v ^ 2 + (algebraMap R S W.a₁ * u + algebraMap R S b3) * v =
      algebraMap R S s * u ^ 3 + algebraMap R S W.a₂ * u ^ 2 +
        algebraMap R S b4 * u + algebraMap R S b6)
    (hp : (W.map (algebraMap R S)).toProjective.Equation
      ![algebraMap R S s * u, algebraMap R S s * v, 1]) :
    Spec.map (CommRingCat.ofHom (evaluation W s b3 b4 b6 u v h).toRingHom) ≫
        toCurve W s b3 b4 b6 h3 h4 h6 =
      WeierstrassIntegralChart.integralChartPoint W 2
        ![algebraMap R S s * u, algebraMap R S s * v, 1] hp rfl := by
  have he : (evaluation W s b3 b4 b6 u v h).comp
      (fromOriginal W s b3 b4 b6 h3 h4 h6) =
        WeierstrassIntegralChart.evaluation W 2
          ![algebraMap R S s * u, algebraMap R S s * v, 1] hp rfl := by
    apply WeierstrassIntegralChart.hom_ext
    intro i
    fin_cases i <;>
      simp [fromOriginal, WeierstrassIntegralChart.evaluation_coord]
  have hr : CommRingCat.ofHom (fromOriginal W s b3 b4 b6 h3 h4 h6).toRingHom ≫
      CommRingCat.ofHom (evaluation W s b3 b4 b6 u v h).toRingHom =
        CommRingCat.ofHom (WeierstrassIntegralChart.evaluation W 2
          ![algebraMap R S s * u, algebraMap R S s * v, 1] hp rfl).toRingHom :=
    congrArg (fun f : WeierstrassIntegralChart.Coordinate W 2 →ₐ[R] S =>
      CommRingCat.ofHom f.toRingHom) he
  change _ ≫ (_ ≫ _) = _ ≫ _
  rw [← Category.assoc, ← Spec.map_comp, hr]

end FLT.Mazur.WeierstrassDilatation
