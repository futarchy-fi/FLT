/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationXFullNodeEqualizer
public import FLT.Mazur.NodeLocalizedPushout

/-!
# Scheme pushout on the original localized first attachment node

The denominator (q+a)(1-c*p²) remains inverted. Both source branches are the
corresponding principal opens, and their marked origins remain the original
scheme-theoretic origin of the attachment chart.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits Polynomial
namespace FLT.Mazur.WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
universe u
variable {K : Type u} [Field K] (a c : K) (ha : IsUnit a)
local notation "s" => fullNodeNormalizedDenominator a c
local notation "hs" => fullNodeNormalizedDenominator_value a c ha
local notation "L" => FullNodeOpen a c

/-- The equalizer spectrum identifies the entire actual attachment open. -/
def fullNodeEqualizerIso : Spec (.of (FullNodeEqualizer a c ha)) ≅ Spec (.of L) :=
  Scheme.Spec.mapIso (fullNodeEqualizerEquiv a c ha).toCommRingCatIso.op

/-- The first localized branch of the original attachment chart. -/
def fullNodeFirstBranch : Spec (.of (Localization.Away (PolygonNodeEqualizer.first s))) ⟶
    Spec (.of L) := NodeLocalDescent.firstBranch K s hs ≫ (fullNodeEqualizerIso a c ha).hom

/-- The second localized branch, retaining the inverted opposite tangent. -/
def fullNodeSecondBranch : Spec (.of (Localization.Away (PolygonNodeEqualizer.second s))) ⟶
    Spec (.of L) := NodeLocalDescent.secondBranch K s hs ≫ (fullNodeEqualizerIso a c ha).hom

/-- The original attachment localization is a pushout in schemes. -/
theorem fullNodeBranches_isPushout :
    IsPushout (NodeLocalDescent.firstOrigin K s hs) (NodeLocalDescent.secondOrigin K s hs)
      (fullNodeFirstBranch a c ha) (fullNodeSecondBranch a c ha) :=
  NodeLocalizedPushout.isPushout_of_iso K s hs (fullNodeEqualizerIso a c ha)

/-- The first pinched origin is exactly the original localized node evaluation. -/
@[reassoc] theorem fullNodeFirstBranch_origin :
    NodeLocalDescent.firstOrigin K s hs ≫ fullNodeFirstBranch a c ha =
      Spec.map (CommRingCat.ofHom (fullNodeOrigin a c ha).toRingHom) := by
  change Spec.map _ ≫ (Spec.map _ ≫ Spec.map _) = Spec.map _
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply IsLocalization.ringHom_ext (Submonoid.powers (fullNodeDenominator a c))
  apply RingHom.ext
  intro x
  change NodeLocalizedEqualizer.evalFirst s hs
    (fullNodeEqualizerEquiv a c ha (algebraMap _ L x)).val.1 =
      fullNodeOrigin a c ha (algebraMap _ L x)
  rw [fullNodeEqualizerEquiv_base, fullNodeOrigin_base]
  change NodeLocalizedEqualizer.evaluation (PolygonNodeEqualizer.first s) 0 _
    (algebraMap K[X] _
      (PolygonNodeEqualizer.first (NodalFiber.polygonNodeEquiv x))) = _
  rw [NodeLocalizedEqualizer.evaluation_algebraMap]
  have he : PolygonNodePresentation.aEval.comp NodalFiber.polygonNodeEquiv.toAlgHom =
      NodalFiber.evaluation (0 : K) 0 0 (by simp) := by
    apply NodalFiber.hom_ext 0 <;> simp [PolygonNodePresentation.aEval]
  exact DFunLike.congr_fun he x

/-- The other branch has the same original node origin. -/
@[reassoc] theorem fullNodeSecondBranch_origin :
    NodeLocalDescent.secondOrigin K s hs ≫ fullNodeSecondBranch a c ha =
      Spec.map (CommRingCat.ofHom (fullNodeOrigin a c ha).toRingHom) :=
  (fullNodeBranches_isPushout a c ha).w.symm.trans (fullNodeFirstBranch_origin a c ha)

end FLT.Mazur.WeierstrassModificationX
