/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientShearRootPositiveNormalization
public import FLT.Mazur.WeierstrassDividedPositiveEqualityPolygonIso
import all FLT.Mazur.WeierstrassDividedPositiveEqualityPushout

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
  (hp : 2 * (start + s + 1) = depth)
local notation "K" => ResidueField R
local notation "p" => coefficientShearGluedStructure hπ data K 0 (s + 1) hs
local notation "E" => coefficientShearGluedOverIso hπ data K 0 (s + 1) hs

local notation "N" => coefficientShearRootPositiveNormalization hπ data D s hs hstart hk hp
local notation "Q" => coefficientShearRootPositiveNodes hπ data D s hs hstart hk

/-- The assembled independent normalization and original nodes give the actual pinching pushout. -/
theorem coefficientShearRootPositiveCocone_isPushout :
    IsPushout (PolygonPinching.toComponents K (2 * s + 4) (by omega))
      (PolygonPinching.toNodes K (2 * s + 4)) N Q := by
  apply (positiveEqualityCycleCocone_isPushout hπ data D s hs hstart hk hp).of_iso'
    (Iso.refl _) (Iso.refl _) (Iso.refl _) E
  · simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]
  · simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]
  · simpa only [Iso.refl_hom, Category.id_comp] using
      (coefficientShearRootPositiveNormalization_original hπ data D s hs hstart hk hp).symm
  · simpa only [Iso.refl_hom, Category.id_comp] using
      (coefficientShearRootPositiveNodes_original hπ data D s hs hstart hk).symm

/-- The same complete diagram is a pushout of underlying schemes. -/
theorem coefficientShearRootPositiveCocone_scheme_isPushout :
    IsPushout (PolygonPinching.toComponents K (2 * s + 4) (by omega)).left
      (PolygonPinching.toNodes K (2 * s + 4)).left (N).left (Q).left :=
  (coefficientShearRootPositiveCocone_isPushout hπ data D s hs hstart hk hp).map (Over.forget _)

/-- The specified polygon compares with the complete independent coefficient cycle. -/
def coefficientShearRootPositivePolygonIso : PolygonAtlas.polygon K (2 * s + 4) ≅ Over.mk p :=
  PolygonPinching.polygonIso K (2 * s + 4) (by omega) N Q
    (coefficientShearRootPositiveCocone_isPushout hπ data D s hs hstart hk hp)

/-- The polygon comparison retains every projective summand of the independent normalization. -/
@[reassoc] theorem coefficientShearRootPositivePolygonIso_normalization :
    PolygonAtlas.normalization K (2 * s + 4) ≫
      (coefficientShearRootPositivePolygonIso hπ data D s hs hstart hk hp).hom = N :=
  PolygonPinching.normalization_polygonIso K (2 * s + 4) (by omega) N Q
    (coefficientShearRootPositiveCocone_isPushout hπ data D s hs hstart hk hp)

/-- The polygon comparison retains the full original node coproduct. -/
@[reassoc] theorem coefficientShearRootPositivePolygonIso_nodes :
    PolygonAtlas.nodes K (2 * s + 4) ≫
      (coefficientShearRootPositivePolygonIso hπ data D s hs hstart hk hp).hom = Q :=
  PolygonPinching.nodes_polygonIso K (2 * s + 4) (by omega) N Q
    (coefficientShearRootPositiveCocone_isPushout hπ data D s hs hstart hk hp)

/-- The independent pinching comparison reconstructs the earlier original-model comparison. -/
@[reassoc] theorem coefficientShearRootPositivePolygonIso_original :
    (coefficientShearRootPositivePolygonIso hπ data D s hs hstart hk hp).hom ≫ (E).hom =
      (positiveEqualityCyclePolygonIso hπ data D s hs hstart hk hp).hom := by
  apply (PolygonAtlas.isPushout K (2 * s + 4) (by omega)).hom_ext
  · rw [← Category.assoc, coefficientShearRootPositivePolygonIso_normalization,
      coefficientShearRootPositiveNormalization_original,
      positiveEqualityCyclePolygonIso_normalization]
  · rw [← Category.assoc, coefficientShearRootPositivePolygonIso_nodes,
      coefficientShearRootPositiveNodes_original, positiveEqualityCyclePolygonIso_nodes]

end FLT.Mazur.WeierstrassDividedDepth
