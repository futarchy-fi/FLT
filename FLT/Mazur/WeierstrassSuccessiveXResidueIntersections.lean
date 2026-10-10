/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSuccessiveXMiddleIntersection
public import FLT.Mazur.WeierstrassSuccessiveXMiddleDisjoint
public import FLT.Mazur.WeierstrassSuccessiveXResidueComponentPoints

/-!
# Full ordered intersections in the actual tensor residue chart

Transport all three middle-component intersection squares through the
constructed residue isomorphism. The conic markings remain the original
ordered markings, and both horizontal lines retain their polynomial origins.
-/

@[expose] public noncomputable section
open IsLocalRing AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassSuccessiveX
open WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} {n : ℕ} (D : SplitNodeDepth W π n)
  (k : ℕ) (hk0 : 0 < k) (hk : 2 * (k + 1) ≤ n) (b3 b4 b6 : R)
  (h3 : W.a₃ = π ^ (k + 1) * b3) (h4 : W.a₄ = π ^ (k + 1) * b4)
local notation "K" => ResidueField R
local notation "W₀" => W.map (residue R)
local notation "a" => residue R W.a₁
local notation "c" => residue R b6
local notation "ha" => D.a₁_unit.map (residue R)
local notation "h2" => Iff.mpr (residue_eq_zero_iff _) D.a₂_mem
local notation "E" => residueRetainedIso D k hk0 hk b3 b4 b6 h3 h4
local notation "C" => residueSuccessiveConicImmersion D k hk0 hk b3 b4 b6 h3 h4
local notation "L₁" => residueSuccessiveLineImmersion D k hk0 hk b3 b4 b6 h3 h4
  0 (middle_first_root W₀)
local notation "L₂" => residueSuccessiveLineImmersion D k hk0 hk b3 b4 b6 h3 h4
  (-a) (middle_second_root W₀)
local notation "o₁" =>
  Spec.map (CommRingCat.ofHom (AlgHom.toRingHom (conicFirstIncidencePoint a c ha)))
local notation "o₂" =>
  Spec.map (CommRingCat.ofHom (AlgHom.toRingHom (conicSecondIncidencePoint a c ha)))
local notation "z" =>
  Spec.map (CommRingCat.ofHom (AlgHom.toRingHom (Polynomial.aeval (0 : K))))

/-- The original first conic marking is the full first tensor component intersection. -/
theorem residueFirstAttachment_isPullback : IsPullback o₁ z C L₁ := by
  have H := middleFirstAttachment_isPullback W₀ c h2 ha
  exact IsPullback.of_isLimit (PullbackCone.isLimitOfCompMono _ _ (E).hom H.cone H.isLimit)

/-- The original opposite marking is the full second tensor component intersection. -/
theorem residueSecondAttachment_isPullback : IsPullback o₂ z C L₂ := by
  have H := middleSecondAttachment_isPullback W₀ c h2 ha
  exact IsPullback.of_isLimit (PullbackCone.isLimitOfCompMono _ _ (E).hom H.cone H.isLimit)

/-- The two ordered tensor lines still have the empty scheme as their full intersection. -/
theorem residueMiddleLines_isPullback :
    IsPullback (Scheme.emptyTo (Spec (.of (Polynomial K))))
      (Scheme.emptyTo (Spec (.of (Polynomial K)))) L₁ L₂ := by
  have H := middleLines_isPullback W₀ c h2 ha
  exact IsPullback.of_isLimit (PullbackCone.isLimitOfCompMono _ _ (E).hom H.cone H.isLimit)

/-- The first full tensor intersection with its ordered projection maps. -/
def residueFirstAttachmentIso : Spec (.of K) ≅ pullback C L₁ :=
  (residueFirstAttachment_isPullback D k hk0 hk b3 b4 b6 h3 h4).isoPullback

/-- The full first intersection projects to the established conic marking. -/
@[reassoc] theorem residueFirstAttachmentIso_conic :
    (residueFirstAttachmentIso D k hk0 hk b3 b4 b6 h3 h4).hom ≫ pullback.fst C L₁ = o₁ :=
  (residueFirstAttachment_isPullback D k hk0 hk b3 b4 b6 h3 h4).isoPullback_hom_fst

/-- The full first intersection projects to the original horizontal line origin. -/
@[reassoc] theorem residueFirstAttachmentIso_line :
    (residueFirstAttachmentIso D k hk0 hk b3 b4 b6 h3 h4).hom ≫ pullback.snd C L₁ = z :=
  (residueFirstAttachment_isPullback D k hk0 hk b3 b4 b6 h3 h4).isoPullback_hom_snd

/-- The second full tensor intersection with its opposite tangent orientation. -/
def residueSecondAttachmentIso : Spec (.of K) ≅ pullback C L₂ :=
  (residueSecondAttachment_isPullback D k hk0 hk b3 b4 b6 h3 h4).isoPullback

/-- The full second intersection projects to the established opposite conic marking. -/
@[reassoc] theorem residueSecondAttachmentIso_conic :
    (residueSecondAttachmentIso D k hk0 hk b3 b4 b6 h3 h4).hom ≫ pullback.fst C L₂ = o₂ :=
  (residueSecondAttachment_isPullback D k hk0 hk b3 b4 b6 h3 h4).isoPullback_hom_fst

/-- The full second intersection projects to the original opposite line origin. -/
@[reassoc] theorem residueSecondAttachmentIso_line :
    (residueSecondAttachmentIso D k hk0 hk b3 b4 b6 h3 h4).hom ≫ pullback.snd C L₂ = z :=
  (residueSecondAttachment_isPullback D k hk0 hk b3 b4 b6 h3 h4).isoPullback_hom_snd

end FLT.Mazur.WeierstrassSuccessiveX
