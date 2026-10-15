/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeNormIndependentGroundTests

/-!
# Constructed envelope transport for Cartesian translation refinements

When the translation is the entire base change of an original translation,
independent new-ground maps give canonically isomorphic envelopes over the
same test. Only the old ground maps agree. The construction preserves the
old translation coordinate, not the new ground coordinate.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace FLT.Mazur.SchemeTranslationNorm
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {R S : Type u} [CommRing R] [CommRing S]
  (a : Spec (.of S) ⟶ Spec (.of R))
  (V : Over (Spec (.of R))) (B W : Over (Spec (.of S)))
  (w : W.left ⟶ V.left) (H : IsPullback w W.hom V.hom a)
  {T : Scheme.{u}} (x : T ⟶ B.left)

/-- The old translation coordinate of the entire independent test envelope. -/
def independentOldTranslation : independentTestEnvelope B W x ⟶ V.left :=
  (prod.snd : prod (independentTest B x) W ⟶ W).left ≫ w

include H in
/-- Pasting the actual Cartesian translation square forgets only the new ground. -/
theorem independentEnvelope_old_isPullback :
    IsPullback (independentTestProjection B W x) (independentOldTranslation V B W w x)
      ((x ≫ B.hom) ≫ a) V.hom := by
  exact (Over.isPullback_of_binaryFan_isLimit _
    (prodIsProd (independentTest B x) W)).paste_vert H.flip

variable (y : T ⟶ B.left) (h : (x ≫ B.hom) ≫ a = (y ≫ B.hom) ≫ a)

/-- Canonical whole-envelope transport between genuinely independent new-ground maps. -/
def cartesianGroundTransport :
    independentTestEnvelope B W x ≅ independentTestEnvelope B W y := by
  have hy := independentEnvelope_old_isPullback a V B W w H y
  rw [← h] at hy
  exact (independentEnvelope_old_isPullback a V B W w H x).isoIsPullback _ _ hy

/-- Transport leaves the entire test projection unchanged. -/
@[reassoc]
theorem cartesianGroundTransport_projection :
    (cartesianGroundTransport a V B W w H x y h).hom ≫
      independentTestProjection B W y = independentTestProjection B W x :=
  IsPullback.isoIsPullback_hom_fst _ _ _ _

/-- Transport also leaves the old independent translation coordinate unchanged. -/
@[reassoc]
theorem cartesianGroundTransport_translation :
    (cartesianGroundTransport a V B W w H x y h).hom ≫
      independentOldTranslation V B W w y = independentOldTranslation V B W w x :=
  IsPullback.isoIsPullback_hom_snd _ _ _ _

/-- These two original coordinates determine the constructed transport uniquely. -/
theorem cartesianGroundTransport_unique
    (g : independentTestEnvelope B W x ⟶ independentTestEnvelope B W y)
    (hp : g ≫ independentTestProjection B W y = independentTestProjection B W x)
    (hw : g ≫ independentOldTranslation V B W w y = independentOldTranslation V B W w x) :
    g = (cartesianGroundTransport a V B W w H x y h).hom := by
  apply (independentEnvelope_old_isPullback a V B W w H y).hom_ext
  · exact hp.trans (cartesianGroundTransport_projection a V B W w H x y h).symm
  · exact hw.trans (cartesianGroundTransport_translation a V B W w H x y h).symm

/-- Constructed transports compose on triple ground overlaps. -/
theorem cartesianGroundTransport_comp (z : T ⟶ B.left)
    (h' : (y ≫ B.hom) ≫ a = (z ≫ B.hom) ≫ a) :
    (cartesianGroundTransport a V B W w H x y h).hom ≫
      (cartesianGroundTransport a V B W w H y z h').hom =
        (cartesianGroundTransport a V B W w H x z (h.trans h')).hom := by
  apply cartesianGroundTransport_unique
  · rw [Category.assoc, cartesianGroundTransport_projection,
      cartesianGroundTransport_projection]
  · rw [Category.assoc, cartesianGroundTransport_translation,
      cartesianGroundTransport_translation]

end FLT.Mazur.SchemeTranslationNorm
