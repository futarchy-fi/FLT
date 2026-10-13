/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientShearResidueInitial
public import FLT.Mazur.WeierstrassCoefficientShearInitialLineOrigins
public import FLT.Mazur.WeierstrassCoefficientShearConicOrigins

import all FLT.Mazur.WeierstrassCoefficientShearResidueInitial

/-!
# Actual initial residue conic origins

The independently completed initial pair starts at the original conic markings
after moving the entire conic to the common final stage.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option quotPrecheck false
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0)
  (hm : maximalIdeal R = Ideal.span {π}) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (s : ℕ) (hs : s + 1 ≤ n) (hk : 2 * (start + (s + 1)) ≤ depth)
  (hstart : 0 < start)
  (h3 : W.a₃ ∈ maximalIdeal R ^ (depth + 1))
  (h4 : W.a₄ ∈ maximalIdeal R ^ (depth + 1))
  (h6 : W.a₆ ∈ maximalIdeal R ^ depth) (hc : IsUnit W.c₄)
local notation "V" => W.map (residue R)
local notation "Q" => AdjoinRoot (nodeTangentPolynomial V)
local notation "r" => AdjoinRoot.root (nodeTangentPolynomial V)
variable [Fact (Irreducible (nodeTangentPolynomial (W.map (residue R))))]
local notation "h1" => show 1 ≤ n from by omega
local notation "hs'" => show 1 + s ≤ n from by omega
local notation "d" => data ⟨0, Nat.zero_lt_succ n⟩
local notation "e" => data ⟨1, Nat.lt_succ_of_le h1⟩
local notation "lin" => nodalDepth_tangent_linear_zero hπ hm e (by dsimp; omega) h3 h4
local notation "ini" => nodalDepth_tangent_linear_zero hπ hm d (by dsimp; omega) h3 h4
local notation "g6" => nodalDepth_tangent_constant_zero hπ hm d (by dsimp; omega) h6
local notation "a" => residueTangentComponentUnit W h3 h4 hc
local notation "ha" => residueTangentComponentUnit_val W h3 h4 hc
local notation "hr" => residueTangentEquation_root W
local notation "hp" => residueTangentEquation_zero W π
  (hm ▸ Ideal.mem_span_singleton_self π)
local notation "hscale" => nodalDepth_tangent_scale_zero (W := W) hm hstart
local notation "C₁" => coefficientShearRootInitialFirstComponent hπ data Q r h1 s hs'
  hscale hp (lin).1 (lin).2 hr (ini).1 (ini).2 g6 a ha
local notation "C₂" => coefficientShearRootInitialSecondComponent hπ data Q r h1 s hs'
  hscale hp (lin).1 (lin).2 hr (ini).1 (ini).2 g6 a ha
local notation "E" => coefficientShearStageIso hπ data Q r (1 + s) (s + 1) hs' hs (by omega)
local notation "g" => coefficientShearGluedStructure hπ data Q r (s + 1) hs
local notation "σ" => coefficientShearResidueTangentConjugation hπ data (s + 1) hs
local notation "f" => tangentResidueConjugationAlgHom (W := W)
local notation "P" => ProjectiveLine.coefficientMap (f).toRingHom

local notation "C" => coefficientShearResidueInitialComponent
  hπ hm data s hs hk hstart h3 h4 h6 hc
local notation "U" => rootShearCurve (W.map (algebraMap R Q)) r
local notation "c" => algebraMap R Q (d).b6
local notation "hu" => Eq.mp (congrArg IsUnit ha) (Units.isUnit a)
local notation "conic" => coefficientShearInitialConic hπ data Q r (s + 1) hs
  hscale (ini).1 (ini).2 hr
open WeierstrassModificationX

/-- Zero on the independent first component is the actual first initial conic marking. -/
@[reassoc] theorem coefficientShearResidueInitialComponent_first_zero :
    ProjectiveLine.zero Q ≫ C 0 =
      Spec.map (CommRingCat.ofHom (conicFirstIncidencePoint (U).a₁ c hu).toRingHom) ≫
        conic := by
  unfold coefficientShearResidueInitialComponent
  simp only [ite_true]
  rw [← Category.assoc, coefficientShearRootInitialFirstComponent_zero]
  simp only [Category.assoc]
  rw [coefficientConicFirstParameter_affine_origin_assoc,
    coefficientShearInitialConic_stageIso]

/-- Zero on the independent opposite component is the original opposite conic marking. -/
@[reassoc] theorem coefficientShearResidueInitialComponent_second_zero :
    ProjectiveLine.zero Q ≫ C 1 =
      Spec.map (CommRingCat.ofHom (conicSecondIncidencePoint (U).a₁ c hu).toRingHom) ≫
        conic := by
  unfold coefficientShearResidueInitialComponent
  rw [ite_eq_right (show (1 : Fin 2) ≠ 0 from by decide)]
  rw [← Category.assoc, coefficientShearRootInitialSecondComponent_zero]
  simp only [Category.assoc]
  rw [coefficientConicSecondParameter_affine_origin_assoc,
    coefficientShearInitialConic_stageIso]

end FLT.Mazur.WeierstrassDividedDepth
