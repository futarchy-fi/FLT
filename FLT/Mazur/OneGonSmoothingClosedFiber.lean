/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OneGonSmoothingMarking
public import FLT.Mazur.OneGonSmoothingCoefficientChange

/-!
# The actual closed fiber of the power-series smoothing

Compose the original pinching comparison with the actual coefficient
pullback. The constant-coefficient fiber is the original one-gon over K.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.OneGonSmoothing
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
universe u
variable {R : Type u} [CommRing R] (K : Type u) [Field K] [Algebra R K]

/-- Changing an equal parameter preserves the actual family structure map. -/
@[reassoc] theorem parameterTransport_structure {a b : R} (h : a = b) :
    eqToHom (congrArg (fun t => (family t).left) h) ≫ (family b).hom = (family a).hom := by
  subst b
  simp

/-- Any zero-parameter coefficient fiber is the original pinched one-gon. -/
def zeroParameterFiberIso (t : R) (ht : algebraMap R K t = 0) :
    OneGonGluing.scheme K ≅
      pullback (family t).hom (Spec.map (CommRingCat.ofHom (algebraMap R K))) :=
  zeroFiberIso K ≪≫ eqToIso (congrArg (fun s => (family s).left) ht.symm) ≪≫
    coefficientPullbackIso t

/-- The coefficient projection is the original one-gon's structure morphism. -/
@[reassoc] theorem zeroParameterFiberIso_snd (t : R) (ht : algebraMap R K t = 0) :
    (zeroParameterFiberIso K t ht).hom ≫ pullback.snd _ _ = OneGonGluing.toBase K := by
  simp only [zeroParameterFiberIso, Iso.trans_hom, Category.assoc,
    coefficientPullbackIso_snd, eqToIso.hom]
  rw [parameterTransport_structure ht.symm]
  exact zeroFiberIso_structure K

/-- The first projection retains the original global coefficient comparison. -/
@[reassoc] theorem zeroParameterFiberIso_fst (t : R) (ht : algebraMap R K t = 0) :
    (zeroParameterFiberIso K t ht).hom ≫ pullback.fst _ _ =
      (zeroFiberIso K).hom ≫
        eqToHom (congrArg (fun s => (family s).left) ht.symm) ≫ coefficientMorphism t := by
  simp only [zeroParameterFiberIso, Iso.trans_hom, Category.assoc,
    coefficientPullbackIso_fst, eqToIso.hom]

/-- Parameter transport preserves the actual infinity marking. -/
@[reassoc] theorem parameterTransport_marking {a b : R} (h : a = b) :
    marking a ≫ eqToHom (congrArg (fun t => (family t).left) h) = marking b := by
  subst b
  simp

/-- The original labeled marking retains its actual curve projection in the coefficient fiber. -/
@[reassoc] theorem zeroParameterFiberIso_marking_fst (t : R)
    (ht : algebraMap R K t = 0) (i : Fin 1) :
    PolygonMarkedSections.sectionMap K 1 (OneGonNormalization.normalizationOver K) 1 i ≫
      (zeroParameterFiberIso K t ht).hom ≫ pullback.fst _ _ =
        Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ marking t := by
  rw [zeroParameterFiberIso_fst]
  simp only [← Category.assoc]
  rw [original_marking_zeroFiberIso, parameterTransport_marking ht.symm,
    marking_coefficientMorphism]

/-- The constant-coefficient closed fiber of the explicit smoothing is the original one-gon. -/
def powerSeriesClosedFiberIso : OneGonGluing.scheme K ≅
    pullback (family (PowerSeries.X : PowerSeries K)).hom
      (Spec.map (CommRingCat.ofHom (PowerSeries.constantCoeff (R := K)))) := by
  let _ : Algebra (PowerSeries K) K := (PowerSeries.constantCoeff (R := K)).toAlgebra
  exact zeroParameterFiberIso K PowerSeries.X PowerSeries.constantCoeff_X

/-- The complete-base closed-fiber comparison retains the original coefficient projection. -/
@[reassoc] theorem powerSeriesClosedFiberIso_snd :
    (powerSeriesClosedFiberIso K).hom ≫ pullback.snd _ _ = OneGonGluing.toBase K := by
  let _ : Algebra (PowerSeries K) K := (PowerSeries.constantCoeff (R := K)).toAlgebra
  exact zeroParameterFiberIso_snd K PowerSeries.X PowerSeries.constantCoeff_X

end FLT.Mazur.OneGonSmoothing
