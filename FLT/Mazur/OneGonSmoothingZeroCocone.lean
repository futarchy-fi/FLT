/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OneGonSmoothingClosedFiber
public import FLT.Mazur.OneGonGlobalPushout

/-!
# The original pinching cocone on every zero-parameter fiber

Transport the actual normalization and node maps through the constructed
comparison. This retains the pushout, including on any specified coefficient square.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.OneGonSmoothing
set_option backward.isDefEq.respectTransparency false
universe u
variable (K : Type u) [Field K]

/-- The zero-parameter cubic retains the original normalization and node pushout. -/
theorem zeroFiber_isPushout :
    IsPushout (PolygonPinching.toComponents K 1 (by decide)) (PolygonPinching.toNodes K 1)
      (OneGonNormalization.normalizationOver K ≫ (zeroFiberOverIso K).hom)
      (OneGonNormalization.nodes K ≫ (zeroFiberOverIso K).hom) :=
  (OneGonGlobalPushout.isPushout K (by decide)).of_iso
    (Iso.refl _) (Iso.refl _) (Iso.refl _) (zeroFiberOverIso K)
    (by simp) (by simp) (by simp) (by simp)

variable {R : Type u} [CommRing R] [Algebra R K] (t : R)
  (ht : algebraMap R K t = 0)
  {Y : Scheme} (p : Y ⟶ (family t).left) (q : Y ⟶ Spec (.of K))
  (hs : IsPullback p q (family t).hom (Spec.map (CommRingCat.ofHom (algebraMap R K))))

/-- The original one-gon comparison on an arbitrary specified coefficient fiber square. -/
def zeroCartesianIso : OneGonGluing.scheme K ≅ Y :=
  zeroParameterFiberIso K t ht ≪≫ hs.isoPullback.symm

/-- The comparison retains the original coefficient projection. -/
@[reassoc] theorem zeroCartesianIso_snd :
    (zeroCartesianIso K t ht p q hs).hom ≫ q = OneGonGluing.toBase K := by
  simp only [zeroCartesianIso, Iso.trans_hom, Iso.symm_hom, Category.assoc,
    IsPullback.isoPullback_inv_snd, zeroParameterFiberIso_snd]

/-- The comparison is an isomorphism over the actual coefficient field. -/
def zeroCartesianOverIso : OneGonNormalization.polygon K ≅ Over.mk q :=
  Over.isoMk (zeroCartesianIso K t ht p q hs) (zeroCartesianIso_snd K t ht p q hs)

/-- Every specified zero-parameter square retains the original normalization pushout. -/
theorem zeroCartesian_isPushout :
    IsPushout (PolygonPinching.toComponents K 1 (by decide)) (PolygonPinching.toNodes K 1)
      (OneGonNormalization.normalizationOver K ≫ (zeroCartesianOverIso K t ht p q hs).hom)
      (OneGonNormalization.nodes K ≫ (zeroCartesianOverIso K t ht p q hs).hom) :=
  (OneGonGlobalPushout.isPushout K (by decide)).of_iso
    (Iso.refl _) (Iso.refl _) (Iso.refl _) (zeroCartesianOverIso K t ht p q hs)
    (by simp) (by simp) (by simp) (by simp)

/-- The original labeled identity retains its curve projection on every such square. -/
@[reassoc] theorem zeroCartesianIso_marking_fst (i : Fin 1) :
    PolygonMarkedSections.sectionMap K 1 (OneGonNormalization.normalizationOver K) 1 i ≫
      (zeroCartesianIso K t ht p q hs).hom ≫ p =
        Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ marking t := by
  simp only [zeroCartesianIso, Iso.trans_hom, Iso.symm_hom, Category.assoc,
    IsPullback.isoPullback_inv_fst]
  exact zeroParameterFiberIso_marking_fst K t ht i

end FLT.Mazur.OneGonSmoothing
