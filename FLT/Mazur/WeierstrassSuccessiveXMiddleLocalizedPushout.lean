/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSuccessiveXMiddleNodeEqualizer
public import FLT.Mazur.NodeLocalizedPushout

/-!
# Scheme pushout on the original middle attachment for arbitrary conic constant

The denominator 1-c*z² remains inverted on the conic parameter branch.
The horizontal branch is an entire affine line, and both origins retain the
original scheme-theoretic attachment point even at equality depth.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits Polynomial
namespace FLT.Mazur.WeierstrassSuccessiveX
set_option backward.isDefEq.respectTransparency false
universe u
variable {K : Type u} [Field K] (c : K)
local notation "s" => middleNodePairDenominator c
local notation "hs" => middleNodePairDenominator_value c
local notation "L" => MiddleNodeOpen c

/-- The equalizer spectrum identifies the entire actual attachment open. -/
def middleNodeLocalizedEqualizerIso : Spec (.of (MiddleNodeEqualizer c)) ≅ Spec (.of L) :=
  Scheme.Spec.mapIso (middleNodeEqualizerEquiv c).toCommRingCatIso.op

/-- The first localized branch of the original attachment chart. -/
def middleNodeLocalizedFirstBranch : Spec (.of (Localization.Away (PolygonNodeEqualizer.first s))) ⟶
    Spec (.of L) := NodeLocalDescent.firstBranch K s hs ≫ (middleNodeLocalizedEqualizerIso c).hom

/-- The second localized branch, whose denominator is identically one. -/
def middleNodeLocalizedSecondBranch :
    Spec (.of (Localization.Away (PolygonNodeEqualizer.second s))) ⟶ Spec (.of L) :=
  NodeLocalDescent.secondBranch K s hs ≫ (middleNodeLocalizedEqualizerIso c).hom

/-- The original attachment localization is a pushout in schemes. -/
theorem middleNodeLocalizedBranches_isPushout :
    IsPushout (NodeLocalDescent.firstOrigin K s hs) (NodeLocalDescent.secondOrigin K s hs)
      (middleNodeLocalizedFirstBranch c) (middleNodeLocalizedSecondBranch c) :=
  NodeLocalizedPushout.isPushout_of_iso K s hs (middleNodeLocalizedEqualizerIso c)

/-- The first pinched origin is exactly the original localized node evaluation. -/
@[reassoc] theorem middleNodeLocalizedFirstBranch_origin :
    NodeLocalDescent.firstOrigin K s hs ≫ middleNodeLocalizedFirstBranch c =
      Spec.map (CommRingCat.ofHom (middleNodeOrigin c).toRingHom) := by
  change Spec.map _ ≫ (Spec.map _ ≫ Spec.map _) = Spec.map _
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply IsLocalization.ringHom_ext (Submonoid.powers (middleNodeDenominator c))
  apply RingHom.ext
  intro x
  change NodeLocalizedEqualizer.evalFirst s hs
    (middleNodeEqualizerEquiv c (algebraMap _ L x)).val.1 =
      middleNodeOrigin c (algebraMap _ L x)
  rw [middleNodeEqualizerEquiv_base, middleNodeOrigin_base]
  change NodeLocalizedEqualizer.evaluation (PolygonNodeEqualizer.first s) 0 _
    (algebraMap K[X] _
      (PolygonNodeEqualizer.first (NodalFiber.polygonNodeEquiv x))) = _
  rw [NodeLocalizedEqualizer.evaluation_algebraMap]
  have he : PolygonNodePresentation.aEval.comp NodalFiber.polygonNodeEquiv.toAlgHom =
      NodalFiber.evaluation (0 : K) 0 0 (by simp) := by
    apply NodalFiber.hom_ext 0 <;> simp [PolygonNodePresentation.aEval]
  exact DFunLike.congr_fun he x

/-- The other branch has the same original node origin. -/
@[reassoc] theorem middleNodeLocalizedSecondBranch_origin :
    NodeLocalDescent.secondOrigin K s hs ≫ middleNodeLocalizedSecondBranch c =
      Spec.map (CommRingCat.ofHom (middleNodeOrigin c).toRingHom) :=
  (middleNodeLocalizedBranches_isPushout c).w.symm.trans (middleNodeLocalizedFirstBranch_origin c)

end FLT.Mazur.WeierstrassSuccessiveX
