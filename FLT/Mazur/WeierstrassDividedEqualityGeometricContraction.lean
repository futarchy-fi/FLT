/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedEqualityCycleCommonNode
public import FLT.Mazur.WeierstrassDividedZeroEqualityPolygonIso
public import FLT.Mazur.PolygonOneGonContractionOriginalCoordinates
import all FLT.Mazur.WeierstrassDividedZeroEqualityPolygonIso

/-!
# The entire equality arithmetic contraction is geometric pinching

The original finite global contraction on the whole closed fiber is the
proved one-gon pinching map followed by the original residue-cubic comparison
and integral coefficient morphism. All nodes and exceptional components are included.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (D : SplitNodeDepth W π depth) (s : ℕ) (hs : s + 1 ≤ n)
  (hk : 2 * (start + s + 1) ≤ depth) (hp : 2 * (start + s + 1) = depth)
local notation "K" => ResidueField R
local notation "q" => Spec.map (CommRingCat.ofHom (algebraMap R K))
local notation "f" => finiteGlobalStructure hπ data (s + 1) hs
local notation "g" => pullback.snd q f ≫ finiteGlobalContraction hπ data (s + 1) hs
variable (hstart : start = 0)
local notation "Z" => zeroEqualityCycleComponent hπ data D s hs hstart hk hp
local notation "hd" => lt_of_lt_of_le (Nat.mul_pos (by decide) (Nat.succ_pos _)) hk
local notation "N" => zeroEqualityCycleNormalization hπ data D s hs hstart hk hp
local notation "Q" => zeroEqualityCycleNodes hπ data D s hs hk
local notation "H" => zeroEqualityCycleCocone_isPushout hπ data D s hs hstart hk hp

/-- The geometric contraction constructed from the actual original pinching pushout. -/
def zeroEqualityOriginalOneGonContraction :
    finiteGlobalTensorModel hπ data K (s + 1) hs ⟶ OneGonGluing.scheme K :=
  (PolygonOneGonContraction.contraction K (2 * s + 2) (by omega) N Q H 0).left

local notation "a" => zeroEqualityOriginalOneGonContraction hπ data D s hs hk hp hstart

/-- The retained complete exterior maps by the original geometric normalization. -/
@[reassoc] theorem zeroEqualityOriginalOneGonContraction_exterior :
    (Z 0).left ≫ a = OneGonNormalization.normalization K := by
  have E := congrArg Over.Hom.left
    (PolygonOneGonContraction.retained_contraction K (2 * s + 2) (by omega) N Q H 0)
  simpa only [zeroEqualityOriginalOneGonContraction,
    zeroEqualityCycleNormalization_ι_assoc, Over.comp_left,
    PolygonOneGonContraction.retainedComponent_left] using E

/-- Every other complete original component maps to the original one-gon node. -/
@[reassoc] theorem zeroEqualityOriginalOneGonContraction_omitted
    (i : Fin (2 * s + 2)) (hi : i ≠ 0) :
    (Z i).left ≫ a = ProjectiveLine.toBase K ≫
      PolygonNodePresentation.bOrigin K ≫ OneGonGluing.node K := by
  have E := congrArg Over.Hom.left
    (PolygonOneGonContraction.omitted_contraction K (2 * s + 2) (by omega) N Q H 0 hi)
  simpa only [zeroEqualityOriginalOneGonContraction,
    zeroEqualityCycleNormalization_ι_assoc, Over.comp_left,
    PolygonOneGonContraction.componentToPoint_left,
    PolygonOneGonContraction.targetNode_left] using E

/-- The full original arithmetic closed-fiber contraction equals the geometric one-gon map. -/
theorem zeroEqualityOriginalOneGonContraction_cubic :
    g = a ≫ (residueOneGonIso D hd).hom ≫
      WeierstrassIntegralChart.integralCoefficientMorphism W := by
  apply zeroEqualityCycleComponent_hom_ext hπ data D s hs hstart hk hp
  intro i
  by_cases hi : i = 0
  · subst i
    rw [zeroEqualityOriginalOneGonContraction_exterior_assoc,
      zeroEqualityCycleComponent_exterior]
    exact finalZeroExteriorComponent_cubicContraction hπ data D s hs hstart hk
  · rw [zeroEqualityOriginalOneGonContraction_omitted_assoc hπ data D s hs hk hp hstart i hi]
    simpa only [Category.assoc] using
      zeroEqualityCycleComponent_cubicContraction hπ data D s hs hk hp hstart i hi

end FLT.Mazur.WeierstrassDividedDepth
