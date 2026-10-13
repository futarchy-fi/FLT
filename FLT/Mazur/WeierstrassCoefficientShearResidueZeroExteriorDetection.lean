/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientShearResidueZeroInitialProjection
public import FLT.Mazur.WeierstrassCoefficientShearResidueZeroExteriorAffine
public import FLT.Mazur.WeierstrassResidueInfinityTensorCover
public import FLT.Mazur.WeierstrassCoefficientShearResidueZeroAdjacentEndpoints
public import FLT.Mazur.WeierstrassCoefficientShearScaleOneEqualityParameterCover
import all FLT.Mazur.WeierstrassCoefficientShearRetainedScaleOneConic
import all FLT.Mazur.WeierstrassCoefficientShearResidueZeroLengthTwoCoconeDescent
import all FLT.Mazur.WeierstrassCoefficientShearResidueZeroTerminalDescent
import all FLT.Mazur.WeierstrassCoefficientShearResidueZeroRetainedCoconeMaps
import all FLT.Mazur.WeierstrassCoefficientShearResidueZeroAtlasCompatibility
import all FLT.Mazur.WeierstrassCoefficientShearResidueZeroAtlasCoconeMaps

import all FLT.Mazur.WeierstrassCoefficientShearResidueZeroCoconeGluing

/-!
# The complete start-zero exterior detects the original incidence and initial charts

Both full chart comparisons take place in the actual common final model.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option quotPrecheck false
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0)
  (hm : maximalIdeal R = Ideal.span {π}) {n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (0 + i.val))
  (s : ℕ) (hs : s + 1 ≤ n) (hk : 2 * (0 + (s + 1)) ≤ depth)
  (h3 : W.a₃ ∈ maximalIdeal R ^ (depth + 1))
  (h4 : W.a₄ ∈ maximalIdeal R ^ (depth + 1))
  (hc : IsUnit W.c₄)
local notation "V" => W.map (residue R)
local notation "Q" => AdjoinRoot (nodeTangentPolynomial V)
local notation "r" => AdjoinRoot.root (nodeTangentPolynomial V)
variable [Fact (Irreducible (nodeTangentPolynomial (W.map (residue R))))]
open WeierstrassModificationX WeierstrassSuccessiveX WeierstrassDilatation
local notation "a" => residueTangentComponentUnit W h3 h4 hc
local notation "ha" => residueTangentComponentUnit_val W h3 h4 hc
local notation "d" => data ⟨1, by omega⟩
local notation "hres" => nodalDepth_residue_uniformizer hm
local notation "lin" => nodalDepth_tangent_linear_zero hπ hm d (by dsimp; omega) h3 h4
local notation "E" => coefficientShearResidueExteriorLift hπ data (s + 1) hs d
  (by dsimp; omega) hres a
local notation "hp" => residueTangentEquation_zero W π
  (hm ▸ Ideal.mem_span_singleton_self π)
local notation "hr" => residueTangentEquation_root W
local notation "L" => Spec.map (CommRingCat.ofHom (tensorShearScaleOneIncidenceMap
  W (π ^ (0 + 0)) π (d).b3 (d).b4 (d).b6 Q r
    (by simp) hp (lin).1 (lin).2 hr).toRingHom)
local notation "B" => coefficientShearRetainedTensorChart
  hπ data Q r (s + 1) hs ⟨0, Nat.zero_lt_succ s⟩
local notation "I" => coefficientShearResidueZeroInitialIso hπ hm data s hs
local notation "U" => rootShearCurve (W.map (algebraMap R Q)) r
local notation "q" => Spec.map (CommRingCat.ofHom
  (algebraMap (Polynomial Q) (SlopeOpen (U).a₁)))
local notation "A" => coefficientShearGluedChart hπ data Q r (s + 1) hs

/-- The entire original exterior affine chart is the incidence line at the final stage. -/
@[reassoc] theorem coefficientShearResidueZeroExteriorLift_incidence :
    ProjectiveLine.left Q ≫ (ProjectiveLine.slopeNormalizationIso a).hom ≫ E = L ≫ B := by
  let J := coefficientShearStageIso hπ data Q r
    (0 + 1 + s) (s + 1) (by omega) hs (by omega)
  have H := congrArg (· ≫ J.hom) (coefficientShearResidueZeroExteriorLift_affine
    hπ data (by omega) s (by omega) hres (lin).1 (lin).2 a)
  simp only [Category.assoc] at H
  rw [coefficientShearResidueExteriorLift_stageIso,
    coefficientShearRetainedScaleOneIncidence, Category.assoc,
    coefficientShearRetainedTensorChart_stageIso] at H
  exact H

include hk

/-- The full initial slope chart factors through the actual complete exterior. -/
@[reassoc] theorem coefficientShearResidueZeroExteriorLift_initial :
    (I).hom ≫ A (.inl 2) =
      q ≫ ProjectiveLine.left Q ≫ (ProjectiveLine.slopeNormalizationIso a).hom ≫ E := by
  rw [coefficientShearResidueZeroInitialIso_glued hπ hm data s hs (lin).1 (lin).2,
    coefficientShearResidueZeroExteriorLift_incidence hπ hm data s hs hk h3 h4 hc]
  rfl

variable {Y : Scheme}
  (u v : coefficientShearGlued hπ data
    (AdjoinRoot (nodeTangentPolynomial (W.map (residue R))))
    (AdjoinRoot.root (nodeTangentPolynomial (W.map (residue R)))) (s + 1) hs ⟶ Y)

/-- Agreement on the full exterior determines the whole original retained incidence line. -/
theorem coefficientShearResidueZeroIncidence_hom_ext (h : E ≫ u = E ≫ v) :
    L ≫ B ≫ u = L ≫ B ≫ v := by
  have H := congrArg (fun f => ProjectiveLine.left Q ≫
    (ProjectiveLine.slopeNormalizationIso a).hom ≫ f) h
  simpa only [coefficientShearResidueZeroExteriorLift_incidence_assoc
    hπ hm data s hs hk h3 h4 hc] using H

/-- Agreement on the full exterior determines the whole initial slope localization. -/
theorem coefficientShearResidueZeroInitialChart_hom_ext (h : E ≫ u = E ≫ v) :
    A (.inl 2) ≫ u = A (.inl 2) ≫ v := by
  apply (cancel_epi (I).hom).mp
  rw [coefficientShearResidueZeroExteriorLift_initial_assoc hπ hm data s hs hk h3 h4 hc,
    coefficientShearResidueZeroExteriorLift_initial_assoc hπ hm data s hs hk h3 h4 hc, h]

end FLT.Mazur.WeierstrassDividedDepth
