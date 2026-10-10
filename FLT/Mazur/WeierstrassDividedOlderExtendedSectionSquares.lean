/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedOlderExtendedSections
public import FLT.Mazur.WeierstrassDividedResidueAtlasExtension

/-!
# Entire coefficient extensions of the ordered sections

Each existing extended section represents the full inverse image of its
original global section. The comparison retains both the global coordinate
and the map from the extended coefficient ring.
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
  (D : SplitNodeDepth W π depth) (j : ℕ) (hj : j + 1 ≤ n)
  (r : ℕ) (hr : j + 1 + r ≤ n)
  (hk0 : 0 < start + j) (hk : 2 * (start + j + 1) ≤ depth)
local notation "K" => ResidueField R
local notation "q" => Spec.map (CommRingCat.ofHom (algebraMap R K))
local notation "f" => finiteGlobalStructure hπ data (j + 1 + r) hr
local notation "first" => olderGlobalFirstSection hπ data D j hj r hr hk0 hk
local notation "second" => olderGlobalSecondSection hπ data D j hj r hr hk0 hk

variable (S : Type u) [CommRing S] [Algebra R S] [Algebra (ResidueField R) S]
  [IsScalarTower R (ResidueField R) S]
local notation "e" => Spec.map (CommRingCat.ofHom (algebraMap K S))
local notation "qS" => Spec.map (CommRingCat.ofHom (algebraMap R S))
local notation "p" => globalResidueExtensionMap hπ data S (j + 1 + r) hr
local notation "H" => globalResidueExtensionMap_isPullback hπ data S (j + 1 + r) hr

/-- The first extended section is the full coefficient pullback of its original section. -/
theorem olderExtendedFirstSection_isPullback :
    IsPullback (olderExtendedFirstSection hπ data D j hj r hr hk0 hk S) e p first := by
  apply (IsPullback.paste_horiz_iff H
    (olderExtendedFirstSection_projection hπ data D j hj r hr hk0 hk S)).mp
  rw [olderExtendedFirstSection_structure, olderGlobalFirstSection_structure]
  exact IsPullback.of_id_fst

/-- The entire first section pullback is the spectrum of the new coefficients. -/
def olderExtendedFirstSectionIso : Spec (.of S) ≅ pullback p first :=
  (olderExtendedFirstSection_isPullback hπ data D j hj r hr hk0 hk S).isoPullback

/-- The first section comparison keeps its actual extended global map. -/
@[reassoc] theorem olderExtendedFirstSectionIso_global :
    (olderExtendedFirstSectionIso hπ data D j hj r hr hk0 hk S).hom ≫
      pullback.fst p first = olderExtendedFirstSection hπ data D j hj r hr hk0 hk S :=
  (olderExtendedFirstSection_isPullback hπ data D j hj r hr hk0 hk S).isoPullback_hom_fst

/-- The first section comparison keeps the original coefficient extension. -/
@[reassoc] theorem olderExtendedFirstSectionIso_original :
    (olderExtendedFirstSectionIso hπ data D j hj r hr hk0 hk S).hom ≫
      pullback.snd p first = e :=
  (olderExtendedFirstSection_isPullback hπ data D j hj r hr hk0 hk S).isoPullback_hom_snd

/-- The second extended section is the full coefficient pullback of its original section. -/
theorem olderExtendedSecondSection_isPullback :
    IsPullback (olderExtendedSecondSection hπ data D j hj r hr hk0 hk S) e p second := by
  apply (IsPullback.paste_horiz_iff H
    (olderExtendedSecondSection_projection hπ data D j hj r hr hk0 hk S)).mp
  rw [olderExtendedSecondSection_structure, olderGlobalSecondSection_structure]
  exact IsPullback.of_id_fst

/-- The entire second section pullback is the spectrum of the new coefficients. -/
def olderExtendedSecondSectionIso : Spec (.of S) ≅ pullback p second :=
  (olderExtendedSecondSection_isPullback hπ data D j hj r hr hk0 hk S).isoPullback

/-- The second section comparison keeps its actual extended global map. -/
@[reassoc] theorem olderExtendedSecondSectionIso_global :
    (olderExtendedSecondSectionIso hπ data D j hj r hr hk0 hk S).hom ≫
      pullback.fst p second = olderExtendedSecondSection hπ data D j hj r hr hk0 hk S :=
  (olderExtendedSecondSection_isPullback hπ data D j hj r hr hk0 hk S).isoPullback_hom_fst

/-- The second section comparison keeps the original coefficient extension. -/
@[reassoc] theorem olderExtendedSecondSectionIso_original :
    (olderExtendedSecondSectionIso hπ data D j hj r hr hk0 hk S).hom ≫
      pullback.snd p second = e :=
  (olderExtendedSecondSection_isPullback hπ data D j hj r hr hk0 hk S).isoPullback_hom_snd

end FLT.Mazur.WeierstrassDividedDepth
