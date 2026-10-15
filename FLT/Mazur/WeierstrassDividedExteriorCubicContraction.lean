/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassResidueOneGonIso
public import FLT.Mazur.WeierstrassDividedZeroExteriorSmoothCoordinates
public import FLT.Mazur.ProjectiveLineScaledEndpointReversal

/-!
# The whole original exterior contracts by the geometric normalization

Equality on the full Laurent torus extends across both endpoints because
the original integral cubic is separated. Thus the two original arithmetic
exterior endpoints map to the same geometric pinched node as scheme maps.
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
  (hstart : start = 0) (hk : 2 * (start + s + 1) ≤ depth)
local notation "K" => ResidueField R
local notation "E" => finalZeroExteriorComponent hπ data D s hs hstart hk
local notation "q" => Spec.map (CommRingCat.ofHom (algebraMap R K))
local notation "f" => finiteGlobalStructure hπ data (s + 1) hs
local notation "g" => finiteGlobalContraction hπ data (s + 1) hs
local notation "hd" => lt_of_lt_of_le (Nat.mul_pos (by decide) (Nat.succ_pos _)) hk
local notation "e" => residueOneGonIso D hd

/-- The entire arithmetic exterior is the geometric normalization under original contraction. -/
@[reassoc] theorem finalZeroExteriorComponent_cubicContraction :
    E ≫ pullback.snd q f ≫ g =
      OneGonNormalization.normalization K ≫ (e).hom ≫ integralCoefficientMorphism W := by
  apply ProjectiveLine.torus_hom_ext K (integralCurveStructure W)
  · simp only [Category.assoc, integralCoefficientMorphism_structure,
      residueOneGonIso_structure_assoc, OneGonNormalization.normalization_toBase_assoc]
    change E ≫ pullback.snd q f ≫ f = ProjectiveLine.toBase K ≫ q
    rw [← pullback.condition, ← Category.assoc, finalZeroExteriorComponent_structure]
  · have H := finalZeroExteriorComponent_torus hπ data D s hs hstart hk
    change (ProjectiveLine.overlapLeft K ≫ ProjectiveLine.left K) ≫ E = _ at H
    simp only [← Category.assoc]
    rw [H, OneGonNormalization.torus_normalization]
    simp only [Category.assoc, finiteGlobalSmoothCoefficientEmbedding_contraction,
      residueOneGonIso_torus_assoc]

/-- The first original exterior endpoint contracts to the geometric one-gon node. -/
@[reassoc] theorem finalZeroExteriorComponent_zero_cubicContraction :
    ProjectiveLine.zero K ≫ E ≫ pullback.snd q f ≫ g =
      PolygonNodePresentation.bOrigin K ≫ OneGonGluing.node K ≫
        (e).hom ≫ integralCoefficientMorphism W := by
  rw [finalZeroExteriorComponent_cubicContraction]
  simp only [← Category.assoc, OneGonNormalization.zero_normalization]

/-- The second original exterior endpoint contracts to that same geometric node. -/
@[reassoc] theorem finalZeroExteriorComponent_infinity_cubicContraction :
    ProjectiveLine.infinity K ≫ E ≫ pullback.snd q f ≫ g =
      PolygonNodePresentation.bOrigin K ≫ OneGonGluing.node K ≫
        (e).hom ≫ integralCoefficientMorphism W := by
  rw [finalZeroExteriorComponent_cubicContraction]
  simp only [← Category.assoc, OneGonNormalization.infinity_normalization]

end FLT.Mazur.WeierstrassDividedDepth
