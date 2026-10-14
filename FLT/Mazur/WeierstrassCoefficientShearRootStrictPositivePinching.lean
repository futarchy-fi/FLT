/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientShearRootStrictPositiveNormalization
public import FLT.Mazur.WeierstrassDividedPositiveSplitPolygonIso
import all FLT.Mazur.WeierstrassDividedPositiveSplitPushout

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
  (hstart : 0 < start) (hk : 2 * (start + s + 1) ≤ depth)
  (hp : 2 * (start + s + 1) < depth)
local notation "K" => ResidueField R
local notation "p" => coefficientShearGluedStructure hπ data K 0 (s + 1) hs
local notation "E" => coefficientShearGluedOverIso hπ data K 0 (s + 1) hs

local notation "N" => coefficientShearRootStrictPositiveNormalization hπ data D s hs hstart hk hp
local notation "Q" => coefficientShearRootStrictPositiveNodes hπ data D s hs hstart hk hp

/-- The assembled independent normalization and original nodes give the actual pinching pushout. -/
theorem coefficientShearRootStrictPositiveCocone_isPushout :
    IsPushout (PolygonPinching.toComponents K (2 * s + 5) (by omega))
      (PolygonPinching.toNodes K (2 * s + 5)) N Q := by
  apply (positiveSplitCycleCocone_isPushout hπ data D s hs hstart hk hp).of_iso'
    (Iso.refl _) (Iso.refl _) (Iso.refl _) E
  · simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]
  · simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]
  · simpa only [Iso.refl_hom, Category.id_comp] using
      (coefficientShearRootStrictPositiveNormalization_original hπ data D s hs hstart hk hp).symm
  · simpa only [Iso.refl_hom, Category.id_comp] using
      (coefficientShearRootStrictPositiveNodes_original hπ data D s hs hstart hk hp).symm

/-- The same complete diagram is a pushout of underlying schemes. -/
theorem coefficientShearRootStrictPositiveCocone_scheme_isPushout :
    IsPushout (PolygonPinching.toComponents K (2 * s + 5) (by omega)).left
      (PolygonPinching.toNodes K (2 * s + 5)).left (N).left (Q).left :=
  (coefficientShearRootStrictPositiveCocone_isPushout
    hπ data D s hs hstart hk hp).map (Over.forget _)

/-- The specified polygon compares with the complete independent coefficient cycle. -/
def coefficientShearRootStrictPositivePolygonIso : PolygonAtlas.polygon K (2 * s + 5) ≅ Over.mk p :=
  PolygonPinching.polygonIso K (2 * s + 5) (by omega) N Q
    (coefficientShearRootStrictPositiveCocone_isPushout hπ data D s hs hstart hk hp)

/-- The polygon comparison retains every projective summand of the independent normalization. -/
@[reassoc] theorem coefficientShearRootStrictPositivePolygonIso_normalization :
    PolygonAtlas.normalization K (2 * s + 5) ≫
      (coefficientShearRootStrictPositivePolygonIso hπ data D s hs hstart hk hp).hom = N :=
  PolygonPinching.normalization_polygonIso K (2 * s + 5) (by omega) N Q
    (coefficientShearRootStrictPositiveCocone_isPushout hπ data D s hs hstart hk hp)

/-- The polygon comparison retains the full original node coproduct. -/
@[reassoc] theorem coefficientShearRootStrictPositivePolygonIso_nodes :
    PolygonAtlas.nodes K (2 * s + 5) ≫
      (coefficientShearRootStrictPositivePolygonIso hπ data D s hs hstart hk hp).hom = Q :=
  PolygonPinching.nodes_polygonIso K (2 * s + 5) (by omega) N Q
    (coefficientShearRootStrictPositiveCocone_isPushout hπ data D s hs hstart hk hp)

/-- The independent pinching comparison reconstructs the earlier original-model comparison. -/
@[reassoc] theorem coefficientShearRootStrictPositivePolygonIso_original :
    (coefficientShearRootStrictPositivePolygonIso hπ data D s hs hstart hk hp).hom ≫ (E).hom =
      (positiveSplitCyclePolygonIso hπ data D s hs hstart hk hp).hom := by
  apply (PolygonAtlas.isPushout K (2 * s + 5) (by omega)).hom_ext
  · rw [← Category.assoc, coefficientShearRootStrictPositivePolygonIso_normalization,
      coefficientShearRootStrictPositiveNormalization_original,
      positiveSplitCyclePolygonIso_normalization]
  · rw [← Category.assoc, coefficientShearRootStrictPositivePolygonIso_nodes,
      coefficientShearRootStrictPositiveNodes_original, positiveSplitCyclePolygonIso_nodes]

end FLT.Mazur.WeierstrassDividedDepth
