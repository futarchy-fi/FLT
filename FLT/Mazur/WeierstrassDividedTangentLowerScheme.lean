/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedTangentLowerContraction

/-!
# Scheme contraction of the smaller-scale branch output

The entire coordinate map and scheme morphism agree with the existing tangent
output. This comparison does not impose smoothness of the original output.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDilatation
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S] [Module.Flat R S]
  (W : WeierstrassCurve R) (s b3 b4 b6 : R)
  (a c : Coordinate W s b3 b4 b6 →ₐ[R] S) (t w a2 b4' b6' e3 e4 e6 : R)
  (ht : IsRegular t) (hs : s = t * w) (h2 : W.a₂ = t * a2) (h3 : W.a₃ = s * b3)
  (h4 : W.a₄ = s * b4) (h6 : W.a₆ = s ^ 2 * b6)
  (h4' : b4 = t * b4') (h6' : b6 = t * b6')
  (he3 : W.a₃ = t * e3) (he4 : W.a₄ = t * e4) (he6 : W.a₆ = t ^ 2 * e6)
local notation "B" => DividedTangentBranchRing W s b3 b4 b6 a c
local notation "e" => dividedTangentBranchRestriction W s b3 b4 b6 a c
local notation "o" => dividedTangentLowerOutput W s b3 b4 b6 a c t w a2 b4' b6' e3 e4 e6
  ht hs h2 h3 h4 h6 h4' h6' he3 he4 he6

/-- The whole original output algebra map is unchanged by the constructed divided lift. -/
theorem dividedTangentLowerOutput_original :
    (o).comp (fromOriginal W t e3 e4 e6 he3 he4 he6) =
      (e).comp (dividedTangentOutput W s b3 b4 b6 a c h3 h4 h6) := by
  apply WeierstrassIntegralChart.hom_ext
  intro i
  fin_cases i
  · change o (fromOriginal W t e3 e4 e6 he3 he4 he6
        (WeierstrassIntegralChart.coord W 2 0)) =
      e (dividedTangentOutput W s b3 b4 b6 a c h3 h4 h6
        (WeierstrassIntegralChart.coord W 2 0))
    simp only [fromOriginal_x, map_mul, AlgHom.commutes,
      dividedTangentLowerOutput_x, dividedTangentOutput,
      WeierstrassIntegralChart.evaluation_coord, Matrix.cons_val_zero]
    exact dividedTangentLowerX_scale W s b3 b4 b6 a c t w a2 b4' b6' hs h2 h4' h6'
  · change o (fromOriginal W t e3 e4 e6 he3 he4 he6
        (WeierstrassIntegralChart.coord W 2 1)) =
      e (dividedTangentOutput W s b3 b4 b6 a c h3 h4 h6
        (WeierstrassIntegralChart.coord W 2 1))
    simp only [fromOriginal_y, map_mul, AlgHom.commutes,
      dividedTangentLowerOutput_y, dividedTangentOutput,
      WeierstrassIntegralChart.evaluation_coord, Matrix.cons_val_one]
    exact dividedTangentLowerY_scale W s b3 b4 b6 a c t w a2 b4' b6' hs h2 h4' h6' h3
  · change ((o).comp (fromOriginal W t e3 e4 e6 he3 he4 he6))
        (WeierstrassIntegralChart.coord W 2 2) =
      ((e).comp (dividedTangentOutput W s b3 b4 b6 a c h3 h4 h6))
        (WeierstrassIntegralChart.coord W 2 2)
    rw [WeierstrassIntegralChart.coord_self, map_one, map_one]

/-- The actual output morphism lands in the divided chart before any smooth-output restriction. -/
def dividedTangentLowerLift : Spec (.of B) ⟶ Spec (.of (Coordinate W t e3 e4 e6)) :=
  Spec.map (CommRingCat.ofHom (o).toRingHom)

/-- Contracting the branch output gives exactly the original tangent morphism. -/
@[reassoc] theorem dividedTangentLowerLift_contraction :
    dividedTangentLowerLift W s b3 b4 b6 a c t w a2 b4' b6' e3 e4 e6
        ht hs h2 h3 h4 h6 h4' h6' he3 he4 he6 ≫
        toCurve W t e3 e4 e6 he3 he4 he6 =
      Spec.map (CommRingCat.ofHom (e).toRingHom) ≫
        dividedTangentToCurve W s b3 b4 b6 a c h3 h4 h6 := by
  unfold dividedTangentLowerLift toCurve dividedTangentToCurve
  rw [← Category.assoc, ← Spec.map_comp, ← Category.assoc, ← Spec.map_comp]
  change Spec.map (CommRingCat.ofHom
    ((o).comp (fromOriginal W t e3 e4 e6 he3 he4 he6)).toRingHom) ≫ _ = _
  rw [dividedTangentLowerOutput_original]
  rfl

end FLT.Mazur.WeierstrassDilatation
