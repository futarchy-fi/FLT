/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedOlderGlobalMiddleComponents
public import FLT.Mazur.WeierstrassDividedOlderGlobalSections
public import FLT.Mazur.WeierstrassSuccessiveXResidueIntersections

/-!
# Full ordered component intersections in the retained global fiber

All three middle-component intersection squares survive the open embedding
of their actual tensor chart. Both conic-line intersections retain their
ordered markings; the two horizontal lines have empty intersection.
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
open WeierstrassSuccessiveX
local notation "K" => ResidueField R
local notation "e" => data (Fin.mk (j + 1) (Nat.lt_succ_of_le hj))
local notation "c" => residue R (Data.b6 e)
local notation "g" => olderGlobalTensorChart hπ data K j hj r hr
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

/-- The first conic marking is the entire corresponding global line intersection. -/
theorem olderGlobalFirstAttachment_isPullback : IsPullback o₁ z C L₁ := by
  have H := residueFirstAttachment_isPullback D (start + j) hk0 hk
    (Data.b3 e) (Data.b4 e) (Data.b6 e) (Data.factor3 e) (Data.factor4 e)
  exact IsPullback.of_isLimit (PullbackCone.isLimitOfCompMono _ _ g H.cone H.isLimit)

/-- The full first global intersection with the original residue base. -/
def olderGlobalFirstAttachmentIso : Spec (.of K) ≅ pullback C L₁ :=
  (olderGlobalFirstAttachment_isPullback hπ data D j hj r hr hk0 hk).isoPullback

/-- The first global comparison preserves its ordered conic marking. -/
@[reassoc] theorem olderGlobalFirstAttachmentIso_conic :
    (olderGlobalFirstAttachmentIso hπ data D j hj r hr hk0 hk).hom ≫
      pullback.fst C L₁ = o₁ :=
  (olderGlobalFirstAttachment_isPullback hπ data D j hj r hr hk0 hk).isoPullback_hom_fst

/-- The first global comparison preserves its original line origin. -/
@[reassoc] theorem olderGlobalFirstAttachmentIso_line :
    (olderGlobalFirstAttachmentIso hπ data D j hj r hr hk0 hk).hom ≫
      pullback.snd C L₁ = z :=
  (olderGlobalFirstAttachment_isPullback hπ data D j hj r hr hk0 hk).isoPullback_hom_snd

/-- The second conic marking is the entire corresponding global line intersection. -/
theorem olderGlobalSecondAttachment_isPullback : IsPullback o₂ z C L₂ := by
  have H := residueSecondAttachment_isPullback D (start + j) hk0 hk
    (Data.b3 e) (Data.b4 e) (Data.b6 e) (Data.factor3 e) (Data.factor4 e)
  exact IsPullback.of_isLimit (PullbackCone.isLimitOfCompMono _ _ g H.cone H.isLimit)

/-- The full second global intersection with the original residue base. -/
def olderGlobalSecondAttachmentIso : Spec (.of K) ≅ pullback C L₂ :=
  (olderGlobalSecondAttachment_isPullback hπ data D j hj r hr hk0 hk).isoPullback

/-- The second global comparison preserves its ordered conic marking. -/
@[reassoc] theorem olderGlobalSecondAttachmentIso_conic :
    (olderGlobalSecondAttachmentIso hπ data D j hj r hr hk0 hk).hom ≫
      pullback.fst C L₂ = o₂ :=
  (olderGlobalSecondAttachment_isPullback hπ data D j hj r hr hk0 hk).isoPullback_hom_fst

/-- The second global comparison preserves its original line origin. -/
@[reassoc] theorem olderGlobalSecondAttachmentIso_line :
    (olderGlobalSecondAttachmentIso hπ data D j hj r hr hk0 hk).hom ≫
      pullback.snd C L₂ = z :=
  (olderGlobalSecondAttachment_isPullback hπ data D j hj r hr hk0 hk).isoPullback_hom_snd

/-- The two ordered retained lines have the empty scheme as their full intersection. -/
theorem olderGlobalMiddleLines_isPullback :
    IsPullback (Scheme.emptyTo (Spec (.of (Polynomial K))))
      (Scheme.emptyTo (Spec (.of (Polynomial K)))) L₁ L₂ := by
  have H := residueMiddleLines_isPullback D (start + j) hk0 hk
    (Data.b3 e) (Data.b4 e) (Data.b6 e) (Data.factor3 e) (Data.factor4 e)
  exact IsPullback.of_isLimit (PullbackCone.isLimitOfCompMono _ _ g H.cone H.isLimit)

/-- The actual global horizontal line images remain disjoint. -/
theorem olderGlobalMiddleLines_disjoint : Disjoint (Set.range L₁) (Set.range L₂) := by
  apply Scheme.isEmpty_pullback_iff.mp
  let E := (olderGlobalMiddleLines_isPullback hπ data D j hj r hr hk0 hk).isoPullback
  exact E.symm.hom.homeomorph.isEmpty

end FLT.Mazur.WeierstrassDividedDepth
