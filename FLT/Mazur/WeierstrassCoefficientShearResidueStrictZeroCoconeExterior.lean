/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientShearResidueStrictZeroCoconeGluing
public import FLT.Mazur.WeierstrassCoefficientShearResidueZeroExteriorAffine
public import FLT.Mazur.WeierstrassResidueInfinityTensorCover
public import FLT.Mazur.WeierstrassCoefficientShearResidueZeroAdjacentEndpoints
public import FLT.Mazur.WeierstrassCoefficientShearScaleOneEqualityParameterCover
import all FLT.Mazur.WeierstrassCoefficientShearRetainedScaleOneConic
import all FLT.Mazur.WeierstrassCoefficientShearResidueStrictZeroAtlasMaps
import all FLT.Mazur.WeierstrassCoefficientShearResidueStrictZeroFirstCoconeDescent
import all FLT.Mazur.WeierstrassCoefficientShearResidueStrictZeroExteriorMaps
import all FLT.Mazur.WeierstrassCoefficientShearResidueStrictZeroCoconeGluing

/-!
# The full strict start-zero exterior restriction

The whole scale-one incidence line and original infinity chart recover the exterior.
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
  (s : ℕ) (hs : s + 1 ≤ n) (hk : 2 * (0 + (s + 1)) < depth)
  (h3 : W.a₃ ∈ maximalIdeal R ^ (depth + 1))
  (h4 : W.a₄ ∈ maximalIdeal R ^ (depth + 1))
  (h6 : W.a₆ ∈ maximalIdeal R ^ depth) (hc : IsUnit W.c₄)
local notation "V" => W.map (residue R)
local notation "Q" => AdjoinRoot (nodeTangentPolynomial V)
local notation "r" => AdjoinRoot.root (nodeTangentPolynomial V)
variable [Fact (Irreducible (nodeTangentPolynomial (W.map (residue R))))]
open WeierstrassModificationX WeierstrassSuccessiveX WeierstrassDilatation
local notation "a" => residueTangentComponentUnit W h3 h4 hc
local notation "ha" => residueTangentComponentUnit_val W h3 h4 hc
variable (C : PushoutCocone (PolygonPinching.toComponents
    (AdjoinRoot (nodeTangentPolynomial (W.map (residue R)))) (2 * s + 3)
    (Nat.zero_lt_succ (2 * s + 2)))
  (PolygonPinching.toNodes
    (AdjoinRoot (nodeTangentPolynomial (W.map (residue R)))) (2 * s + 3)))
local notation "F" => PolygonCyclicPushout.inputComponent Q (2 * s + 3) C.inl
local notation "w" => fun i => by
  simpa only [PolygonCyclicAtlas.next_eq_rotate] using
    PolygonCyclicPushout.input_condition Q (2 * s + 3) (by omega) C.inl C.inr C.condition i

local notation "A" => coefficientShearAtlasMap hπ data Q r (s + 1) hs
local notation "D" => coefficientShearResidueStrictZeroAtlasCoconeMap
  hπ hm data s hs hk h3 h4 h6 hc C
local notation "hp" => residueTangentEquation_zero W π
  (hm ▸ Ideal.mem_span_singleton_self π)

local notation "cover" => coefficientShearGluingCover hπ data Q r (s + 1) hs
local notation "G" => coefficientShearGluedIso hπ data Q r (s + 1) hs

local notation "M" => coefficientShearResidueStrictZeroGluedCoconeDesc
  hπ hm data s hs hk h3 h4 h6 hc C
local notation "d" => data ⟨1, by omega⟩
local notation "hres" => nodalDepth_residue_uniformizer hm
local notation "lin" => nodalDepth_tangent_linear_zero hπ hm d (by dsimp; omega) h3 h4
local notation "E" => coefficientShearResidueExteriorLift hπ data (s + 1) hs d
  (by dsimp; omega) hres a

/-- The complete original exterior recovers the zero summand, including length three. -/
theorem coefficientShearResidueStrictZeroGluedCoconeDesc_exterior : E ≫ M = F 0 := by
  apply (cancel_epi (ProjectiveLine.slopeNormalizationIso a).hom).mp
  apply residueInfinityTensorParameter_hom_ext d (by dsimp; omega) hres a ha
  · let J := coefficientShearStageIso hπ data Q r
      (0 + 1 + s) (s + 1) (by omega) hs (by omega)
    have H := congrArg (· ≫ J.hom) (coefficientShearResidueZeroExteriorLift_affine
      hπ data (by omega) s (by omega) hres (lin).1 (lin).2 a)
    simp only [Category.assoc] at H
    rw [coefficientShearResidueExteriorLift_stageIso,
      coefficientShearRetainedScaleOneIncidence, Category.assoc,
      coefficientShearRetainedTensorChart_stageIso] at H
    rw [← Category.assoc, ← Category.assoc,
      Category.assoc (ProjectiveLine.left Q), H]
    simp only [coefficientShearRetainedTensorChart, Category.assoc]
    rw [coefficientShearResidueStrictZeroGluedCoconeDesc_chart]
    rw [coefficientShearResidueStrictZeroAtlasCoconeMap]
    change _ ≫ _ ≫ coefficientShearResidueStrictZeroFirstCoconeDesc
      hπ hm data s hs hk h3 h4 h6 hc C = _
    exact coefficientShearResidueStrictZeroFirstCoconeDesc_exterior
      hπ hm data s hs hk h3 h4 h6 hc C
  · rw [coefficientShearResidueExteriorLift_infinityChart_assoc,
      coefficientShearResidueStrictZeroGluedCoconeDesc_chart,
      coefficientShearResidueStrictZeroAtlasCoconeMap_infinity,
      coefficientShearResidueStrictZeroInfinityCoconeDesc]

end FLT.Mazur.WeierstrassDividedDepth
