/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedOlderExtendedSectionSquares
public import FLT.Mazur.WeierstrassDividedOlderExtendedComponentOrigins
public import FLT.Mazur.WeierstrassDividedOlderGlobalIntersections
public import FLT.Mazur.PullbackOverlapBaseChange
public import FLT.Mazur.WeierstrassDividedOlderGlobalComponentSections

/-!
# Full ordered conic-line intersections after coefficient extension

The existing conic and line origins are the actual pullback projections of
the entire extended components. Their intersection is precisely Spec of the
new coefficient ring, with the original ordering and global sections.
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
  (S : Type u) [CommRing S] [Algebra R S] [Algebra (ResidueField R) S]
  [IsScalarTower R (ResidueField R) S]
open WeierstrassSuccessiveX
local notation "K" => ResidueField R
local notation "e" => Spec.map (CommRingCat.ofHom (algebraMap K S))
local notation "p" => globalResidueExtensionMap hπ data S (j + 1 + r) hr
local notation "d" => data (Fin.mk (j + 1) (Nat.lt_succ_of_le hj))
local notation "c" => residue R (Data.b6 d)
local notation "first" => olderExtendedFirstSection hπ data D j hj r hr hk0 hk S
local notation "second" => olderExtendedSecondSection hπ data D j hj r hr hk0 hk S
open WeierstrassModificationX
local notation "a" => residue R W.a₁
local notation "ha" => D.a₁_unit.map (residue R)
local notation "C" => olderGlobalMiddleConic hπ data D j hj r hr hk0 hk
local notation "L₁" => olderGlobalMiddleFirstLine hπ data D j hj r hr hk0 hk
local notation "L₂" => olderGlobalMiddleSecondLine hπ data D j hj r hr hk0 hk
local notation "o₁" =>
  Spec.map (CommRingCat.ofHom (AlgHom.toRingHom (conicFirstIncidencePoint a c ha)))
local notation "o₂" =>
  Spec.map (CommRingCat.ofHom (AlgHom.toRingHom (conicSecondIncidencePoint a c ha)))
local notation "z" =>
  Spec.map (CommRingCat.ofHom (AlgHom.toRingHom (Polynomial.aeval (0 : K))))

/-- The first pair of existing origins is the full extended component intersection. -/
theorem olderExtendedFirstAttachment_isPullback :
    IsPullback (olderExtendedFirstConicOrigin hπ data D j hj r hr hk0 hk S)
      (olderExtendedFirstLineOrigin hπ data D j hj r hr hk0 hk S)
      (pullback.fst p C) (pullback.fst p L₁) := by
  have Q : IsPullback first e p (o₁ ≫ C) := by
    rw [olderGlobalFirstSection_conic]
    exact olderExtendedFirstSection_isPullback hπ data D j hj r hr hk0 hk S
  have H := olderGlobalFirstAttachment_isPullback hπ data D j hj r hr hk0 hk
  apply (PullbackOverlapBaseChange.isPullback H p).of_iso' Q.isoPullback
    (Iso.refl _) (Iso.refl _) (Iso.refl _)
  · simp only [Iso.refl_hom, Category.comp_id]
    apply pullback.hom_ext
    · rw [Category.assoc, PullbackOverlapBaseChange.first_fst,
        Q.isoPullback_hom_fst, olderExtendedFirstConicOrigin_global]
    · rw [Category.assoc, PullbackOverlapBaseChange.first_snd,
        Q.isoPullback_hom_snd_assoc, olderExtendedFirstConicOrigin_original]
  · simp only [Iso.refl_hom, Category.comp_id]
    apply pullback.hom_ext
    · rw [Category.assoc, PullbackOverlapBaseChange.second_fst,
        Q.isoPullback_hom_fst, olderExtendedFirstLineOrigin_global]
    · rw [Category.assoc, PullbackOverlapBaseChange.second_snd,
        Q.isoPullback_hom_snd_assoc, olderExtendedFirstLineOrigin_original]
  · simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]
  · simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]

/-- The entire first extended intersection is the new coefficient spectrum. -/
def olderExtendedFirstAttachmentIso : Spec (.of S) ≅
    pullback (pullback.fst p C) (pullback.fst p L₁) :=
  (olderExtendedFirstAttachment_isPullback hπ data D j hj r hr hk0 hk S).isoPullback

/-- The first extended intersection comparison retains its original conic origin. -/
@[reassoc] theorem olderExtendedFirstAttachmentIso_conic :
    (olderExtendedFirstAttachmentIso hπ data D j hj r hr hk0 hk S).hom ≫
      pullback.fst (pullback.fst p C) (pullback.fst p L₁) =
        olderExtendedFirstConicOrigin hπ data D j hj r hr hk0 hk S :=
  (olderExtendedFirstAttachment_isPullback hπ data D j hj r hr hk0 hk S).isoPullback_hom_fst

/-- The first extended intersection comparison retains its original line origin. -/
@[reassoc] theorem olderExtendedFirstAttachmentIso_line :
    (olderExtendedFirstAttachmentIso hπ data D j hj r hr hk0 hk S).hom ≫
      pullback.snd (pullback.fst p C) (pullback.fst p L₁) =
        olderExtendedFirstLineOrigin hπ data D j hj r hr hk0 hk S :=
  (olderExtendedFirstAttachment_isPullback hπ data D j hj r hr hk0 hk S).isoPullback_hom_snd

/-- The second pair of existing origins is the full extended component intersection. -/
theorem olderExtendedSecondAttachment_isPullback :
    IsPullback (olderExtendedSecondConicOrigin hπ data D j hj r hr hk0 hk S)
      (olderExtendedSecondLineOrigin hπ data D j hj r hr hk0 hk S)
      (pullback.fst p C) (pullback.fst p L₂) := by
  have Q : IsPullback second e p (o₂ ≫ C) := by
    rw [olderGlobalSecondSection_conic]
    exact olderExtendedSecondSection_isPullback hπ data D j hj r hr hk0 hk S
  have H := olderGlobalSecondAttachment_isPullback hπ data D j hj r hr hk0 hk
  apply (PullbackOverlapBaseChange.isPullback H p).of_iso' Q.isoPullback
    (Iso.refl _) (Iso.refl _) (Iso.refl _)
  · simp only [Iso.refl_hom, Category.comp_id]
    apply pullback.hom_ext
    · rw [Category.assoc, PullbackOverlapBaseChange.first_fst,
        Q.isoPullback_hom_fst, olderExtendedSecondConicOrigin_global]
    · rw [Category.assoc, PullbackOverlapBaseChange.first_snd,
        Q.isoPullback_hom_snd_assoc, olderExtendedSecondConicOrigin_original]
  · simp only [Iso.refl_hom, Category.comp_id]
    apply pullback.hom_ext
    · rw [Category.assoc, PullbackOverlapBaseChange.second_fst,
        Q.isoPullback_hom_fst, olderExtendedSecondLineOrigin_global]
    · rw [Category.assoc, PullbackOverlapBaseChange.second_snd,
        Q.isoPullback_hom_snd_assoc, olderExtendedSecondLineOrigin_original]
  · simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]
  · simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]

/-- The entire second extended intersection is the new coefficient spectrum. -/
def olderExtendedSecondAttachmentIso : Spec (.of S) ≅
    pullback (pullback.fst p C) (pullback.fst p L₂) :=
  (olderExtendedSecondAttachment_isPullback hπ data D j hj r hr hk0 hk S).isoPullback

/-- The second extended intersection comparison retains its original conic origin. -/
@[reassoc] theorem olderExtendedSecondAttachmentIso_conic :
    (olderExtendedSecondAttachmentIso hπ data D j hj r hr hk0 hk S).hom ≫
      pullback.fst (pullback.fst p C) (pullback.fst p L₂) =
        olderExtendedSecondConicOrigin hπ data D j hj r hr hk0 hk S :=
  (olderExtendedSecondAttachment_isPullback hπ data D j hj r hr hk0 hk S).isoPullback_hom_fst

/-- The second extended intersection comparison retains its original line origin. -/
@[reassoc] theorem olderExtendedSecondAttachmentIso_line :
    (olderExtendedSecondAttachmentIso hπ data D j hj r hr hk0 hk S).hom ≫
      pullback.snd (pullback.fst p C) (pullback.fst p L₂) =
        olderExtendedSecondLineOrigin hπ data D j hj r hr hk0 hk S :=
  (olderExtendedSecondAttachment_isPullback hπ data D j hj r hr hk0 hk S).isoPullback_hom_snd

end FLT.Mazur.WeierstrassDividedDepth
