/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedTangentBranchContraction

/-!
# The exact original contraction of the constructed branch output

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
  (a c : Coordinate W s b3 b4 b6 →ₐ[R] S) (a2 b4' b6' : R) (hs : IsRegular s)
  (h2 : W.a₂ = s * a2) (h3 : W.a₃ = s * b3)
  (h4 : W.a₄ = s * b4) (h6 : W.a₆ = s ^ 2 * b6)
  (h4' : b4 = s * b4') (h6' : b6 = s * b6')
local notation "B" => DividedTangentBranchRing W s b3 b4 b6 a c
local notation "e" => dividedTangentBranchRestriction W s b3 b4 b6 a c
local notation "o" => dividedTangentBranchOutput W s b3 b4 b6 a c a2 b4' b6'
  hs h2 h3 h4 h6 h4' h6'

/-- The whole original output algebra map is unchanged by the constructed divided lift. -/
theorem dividedTangentBranchOutput_original :
    (o).comp (fromOriginal W s b3 b4 b6 h3 h4 h6) =
      (e).comp (dividedTangentOutput W s b3 b4 b6 a c h3 h4 h6) := by
  apply WeierstrassIntegralChart.hom_ext
  intro i
  fin_cases i
  · change o (fromOriginal W s b3 b4 b6 h3 h4 h6
        (WeierstrassIntegralChart.coord W 2 0)) =
      e (dividedTangentOutput W s b3 b4 b6 a c h3 h4 h6
        (WeierstrassIntegralChart.coord W 2 0))
    simp only [fromOriginal_x, map_mul, AlgHom.commutes,
      dividedTangentBranchOutput_x, dividedTangentOutput,
      WeierstrassIntegralChart.evaluation_coord, Matrix.cons_val_zero]
    exact dividedTangentBranchX_scale W s b3 b4 b6 a c a2 b4' b6' h2 h4' h6'
  · change o (fromOriginal W s b3 b4 b6 h3 h4 h6
        (WeierstrassIntegralChart.coord W 2 1)) =
      e (dividedTangentOutput W s b3 b4 b6 a c h3 h4 h6
        (WeierstrassIntegralChart.coord W 2 1))
    simp only [fromOriginal_y, map_mul, AlgHom.commutes,
      dividedTangentBranchOutput_y, dividedTangentOutput,
      WeierstrassIntegralChart.evaluation_coord, Matrix.cons_val_one]
    exact dividedTangentBranchY_scale W s b3 b4 b6 a c a2 b4' b6' h2 h4' h6' h3
  · change ((o).comp (fromOriginal W s b3 b4 b6 h3 h4 h6))
        (WeierstrassIntegralChart.coord W 2 2) =
      ((e).comp (dividedTangentOutput W s b3 b4 b6 a c h3 h4 h6))
        (WeierstrassIntegralChart.coord W 2 2)
    rw [WeierstrassIntegralChart.coord_self, map_one, map_one]

/-- The actual output morphism lands in the divided chart before any smooth-output restriction. -/
def dividedTangentBranchLift : Spec (.of B) ⟶ Spec (.of (Coordinate W s b3 b4 b6)) :=
  Spec.map (CommRingCat.ofHom (o).toRingHom)

/-- Contracting the branch output gives exactly the original tangent morphism. -/
@[reassoc] theorem dividedTangentBranchLift_contraction :
    dividedTangentBranchLift W s b3 b4 b6 a c a2 b4' b6' hs h2 h3 h4 h6 h4' h6' ≫
        toCurve W s b3 b4 b6 h3 h4 h6 =
      Spec.map (CommRingCat.ofHom (e).toRingHom) ≫
        dividedTangentToCurve W s b3 b4 b6 a c h3 h4 h6 := by
  unfold dividedTangentBranchLift toCurve dividedTangentToCurve
  rw [← Category.assoc, ← Spec.map_comp, ← Category.assoc, ← Spec.map_comp]
  change Spec.map (CommRingCat.ofHom
    ((o).comp (fromOriginal W s b3 b4 b6 h3 h4 h6)).toRingHom) ≫ _ = _
  rw [dividedTangentBranchOutput_original]
  rfl

end FLT.Mazur.WeierstrassDilatation
