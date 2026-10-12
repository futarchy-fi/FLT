/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientShearRootZeroNormalization
public import FLT.Mazur.WeierstrassDividedZeroCyclePolygonIso
import all FLT.Mazur.WeierstrassDividedZeroCyclePushout

/-!
# The independent coefficient cycle gives the original pinching pushout

Transport the proved original universal property along the complete comparison
of the independently assembled normalization and every actual node section.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (D : SplitNodeDepth W π depth) (s : ℕ) (hs : s + 1 ≤ n)
  (hstart : start = 0) (hk : 2 * (start + s + 1) ≤ depth)
  (hp : 2 * (start + s + 1) < depth)
local notation "K" => ResidueField R
local notation "p" => coefficientShearGluedStructure hπ data K 0 (s + 1) hs
local notation "E" => coefficientShearGluedOverIso hπ data K 0 (s + 1) hs

local notation "N" => coefficientShearRootZeroNormalization hπ data D s hs hstart hk hp
local notation "Q" => coefficientShearRootZeroNodes hπ data D s hs hk hp

/-- The assembled independent normalization and original nodes give the actual pinching pushout. -/
theorem coefficientShearRootZeroCocone_isPushout :
    IsPushout (PolygonPinching.toComponents K (2 * s + 3) (by omega))
      (PolygonPinching.toNodes K (2 * s + 3)) N Q := by
  apply (zeroSplitCycleCocone_isPushout hπ data D s hs hstart hp).of_iso'
    (Iso.refl _) (Iso.refl _) (Iso.refl _) E
  · simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]
  · simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]
  · simpa only [Iso.refl_hom, Category.id_comp] using
      (coefficientShearRootZeroNormalization_original hπ data D s hs hstart hk hp).symm
  · simpa only [Iso.refl_hom, Category.id_comp] using
      (coefficientShearRootZeroNodes_original hπ data D s hs hk hp).symm

/-- The same complete diagram is a pushout of underlying schemes. -/
theorem coefficientShearRootZeroCocone_scheme_isPushout :
    IsPushout (PolygonPinching.toComponents K (2 * s + 3) (by omega)).left
      (PolygonPinching.toNodes K (2 * s + 3)).left (N).left (Q).left :=
  (coefficientShearRootZeroCocone_isPushout hπ data D s hs hstart hk hp).map (Over.forget _)

/-- The specified polygon compares with the complete independent coefficient cycle. -/
def coefficientShearRootZeroPolygonIso : PolygonAtlas.polygon K (2 * s + 3) ≅ Over.mk p :=
  PolygonPinching.polygonIso K (2 * s + 3) (by omega) N Q
    (coefficientShearRootZeroCocone_isPushout hπ data D s hs hstart hk hp)

/-- The polygon comparison retains every projective summand of the independent normalization. -/
@[reassoc] theorem coefficientShearRootZeroPolygonIso_normalization :
    PolygonAtlas.normalization K (2 * s + 3) ≫
      (coefficientShearRootZeroPolygonIso hπ data D s hs hstart hk hp).hom = N :=
  PolygonPinching.normalization_polygonIso K (2 * s + 3) (by omega) N Q
    (coefficientShearRootZeroCocone_isPushout hπ data D s hs hstart hk hp)

/-- The polygon comparison retains the full original node coproduct. -/
@[reassoc] theorem coefficientShearRootZeroPolygonIso_nodes :
    PolygonAtlas.nodes K (2 * s + 3) ≫
      (coefficientShearRootZeroPolygonIso hπ data D s hs hstart hk hp).hom = Q :=
  PolygonPinching.nodes_polygonIso K (2 * s + 3) (by omega) N Q
    (coefficientShearRootZeroCocone_isPushout hπ data D s hs hstart hk hp)

/-- The independent pinching comparison reconstructs the earlier original-model comparison. -/
@[reassoc] theorem coefficientShearRootZeroPolygonIso_original :
    (coefficientShearRootZeroPolygonIso hπ data D s hs hstart hk hp).hom ≫ (E).hom =
      (zeroSplitCyclePolygonIso hπ data D s hs hstart hp).hom := by
  apply (PolygonAtlas.isPushout K (2 * s + 3) (by omega)).hom_ext
  · rw [← Category.assoc, coefficientShearRootZeroPolygonIso_normalization,
      coefficientShearRootZeroNormalization_original, zeroSplitCyclePolygonIso_normalization]
  · rw [← Category.assoc, coefficientShearRootZeroPolygonIso_nodes,
      coefficientShearRootZeroNodes_original, zeroSplitCyclePolygonIso_nodes]

end FLT.Mazur.WeierstrassDividedDepth
