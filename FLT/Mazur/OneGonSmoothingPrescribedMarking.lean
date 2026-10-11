/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OneGonSmoothingMarkedFamily
public import FLT.Mazur.PolygonMarkedScaling

/-!
# Prescribed unit markings on the original one-gon

Translate the original pinching before its comparison with the explicit smoothing.
Every prescribed unit-valued labeled section then becomes the actual infinity marking.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.OneGonSmoothing
set_option backward.isDefEq.respectTransparency false
variable (K : Type) [Field K]

/-- Translation of the original one-gon taking its prescribed unit marking to one. -/
def prescribedMarkingTranslation (a : Kˣ) :
    OneGonNormalization.polygon K ≅ OneGonNormalization.polygon K :=
  PolygonPinching.polygonScalingIso K (by decide)
    (OneGonNormalization.normalizationOver K) (OneGonNormalization.nodes K)
    (OneGonGlobalPushout.isPushout K (by decide)) a⁻¹

/-- The actual translation retains the label and normalizes the unit marking. -/
@[reassoc] theorem prescribedMarkingTranslation_section (a : Kˣ) (i : Fin 1) :
    PolygonMarkedSections.sectionMap K 1 (OneGonNormalization.normalizationOver K) a i ≫
      (prescribedMarkingTranslation K a).hom.left =
        PolygonMarkedSections.sectionMap K 1 (OneGonNormalization.normalizationOver K) 1 i :=
  PolygonMarkedScaling.section_inverse_scaling K 1 (by decide) _ _
    (OneGonGlobalPushout.isPushout K (by decide)) a i

/-- The zero-cubic comparison with any prescribed unit marking on the original one-gon. -/
def prescribedZeroFiberOverIso (a : Kˣ) :
    OneGonNormalization.polygon K ≅ family (0 : K) :=
  prescribedMarkingTranslation K a ≪≫ zeroFiberOverIso K

/-- The prescribed original labeled marking is exactly the zero cubic's infinity section. -/
@[reassoc] theorem prescribedZeroFiberOverIso_section (a : Kˣ) (i : Fin 1) :
    PolygonMarkedSections.sectionMap K 1 (OneGonNormalization.normalizationOver K) a i ≫
      (prescribedZeroFiberOverIso K a).hom.left = marking (0 : K) := by
  change _ ≫ (prescribedMarkingTranslation K a).hom.left ≫ (zeroFiberIso K).hom = _
  rw [prescribedMarkingTranslation_section_assoc, original_marking_zeroFiberIso]

/-- The actual complete closed fiber with a prescribed marking on the original one-gon. -/
def prescribedClosedFiberIso (a : Kˣ) : OneGonGluing.scheme K ≅
    pullback (family (PowerSeries.X : PowerSeries K)).hom
      (Spec.map (CommRingCat.ofHom (PowerSeries.constantCoeff (R := K)))) :=
  (Over.forget _).mapIso (prescribedMarkingTranslation K a) ≪≫ powerSeriesClosedFiberIso K

/-- The prescribed complete closed-fiber comparison retains the actual coefficient field. -/
@[reassoc] theorem prescribedClosedFiberIso_snd (a : Kˣ) :
    (prescribedClosedFiberIso K a).hom ≫ pullback.snd _ _ = OneGonGluing.toBase K := by
  simp only [prescribedClosedFiberIso, Iso.trans_hom, Functor.mapIso_hom, Over.forget_map,
    Category.assoc, powerSeriesClosedFiberIso_snd]
  exact (prescribedMarkingTranslation K a).hom.w

/-- Every prescribed original marking becomes the actual infinity section of the closed fiber. -/
@[reassoc] theorem prescribedClosedFiberIso_section (a : Kˣ) (i : Fin 1) :
    PolygonMarkedSections.sectionMap K 1 (OneGonNormalization.normalizationOver K) a i ≫
      (prescribedClosedFiberIso K a).hom =
        fiberMarking (PowerSeries.X : PowerSeries K)
          (Spec.map (CommRingCat.ofHom (PowerSeries.constantCoeff (R := K)))) := by
  change _ ≫ (prescribedMarkingTranslation K a).hom.left ≫ (powerSeriesClosedFiberIso K).hom = _
  rw [prescribedMarkingTranslation_section_assoc, original_marking_closedFiber]

variable {R : Type} [CommRing R] [Algebra R K] (t : R)
  (ht : algebraMap R K t = 0)
  {Y : Scheme} (p : Y ⟶ (family t).left) (q : Y ⟶ Spec (.of K))
  (hs : IsPullback p q (family t).hom (Spec.map (CommRingCat.ofHom (algebraMap R K))))

/-- The prescribed marking comparison on any specified zero-parameter coefficient square. -/
def prescribedZeroCartesianIso (a : Kˣ) : OneGonGluing.scheme K ≅ Y :=
  (Over.forget _).mapIso (prescribedMarkingTranslation K a) ≪≫ zeroCartesianIso K t ht p q hs

/-- The prescribed cartesian comparison retains the original coefficient projection. -/
@[reassoc] theorem prescribedZeroCartesianIso_snd (a : Kˣ) :
    (prescribedZeroCartesianIso K t ht p q hs a).hom ≫ q = OneGonGluing.toBase K := by
  simp only [prescribedZeroCartesianIso, Iso.trans_hom, Functor.mapIso_hom, Over.forget_map,
    Category.assoc, zeroCartesianIso_snd]
  exact (prescribedMarkingTranslation K a).hom.w

/-- Every prescribed label has the actual infinity curve projection on the specified square. -/
@[reassoc] theorem prescribedZeroCartesianIso_section_fst (a : Kˣ) (i : Fin 1) :
    PolygonMarkedSections.sectionMap K 1 (OneGonNormalization.normalizationOver K) a i ≫
      (prescribedZeroCartesianIso K t ht p q hs a).hom ≫ p =
        Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ marking t := by
  simp only [prescribedZeroCartesianIso, Iso.trans_hom, Functor.mapIso_hom, Over.forget_map,
    Category.assoc, prescribedMarkingTranslation_section_assoc, zeroCartesianIso_marking_fst]

end FLT.Mazur.OneGonSmoothing
