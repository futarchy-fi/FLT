/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSuccessiveFractionAction
public import FLT.Mazur.WeierstrassSuccessiveOriginalOpen
public import FLT.Mazur.RegularCenterSeparatedLiftExt

/-!
# Actual local successor action lifts and their uniqueness

Transport the constructed Rees lift into the existing two-chart successor
modification. Its contraction is the genuine divided output, and regular
principalization makes it the unique such lift on the entire presentation.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassSuccessiveX
open WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R]
  (W : WeierstrassCurve R) (s π b3 b4 b6 : R)
  (h3 : W.a₃ = s * (π * b3)) (h4 : W.a₄ = s * (π * b4))
  (h6 : W.a₆ = s ^ 2 * (π ^ 2 * b6))
local notation "B" =>
  WeierstrassDilatation.Coordinate W s (π * b3) (π * b4) (π ^ 2 * b6)
local notation "c" =>
  WeierstrassDilatation.fromOriginal W s (π * b3) (π * b4) (π ^ 2 * b6) h3 h4 h6
variable {S : Type u} [CommRing S] [Algebra R S]
variable (p : Spec (.of S) ⟶ (integralSmoothOpen W).toScheme)
  (α β : WeierstrassDilatation.Coordinate W s
    (π * b3) (π * b4) (π ^ 2 * b6) →ₐ[R] S)
  (hp : p ≫ integralSmoothStructure W =
    (Spec.map (CommRingCat.ofHom (β.comp (WeierstrassDilatation.fromOriginal W s
      (π * b3) (π * b4) (π ^ 2 * b6) h3 h4 h6)).toRingHom) ≫ integralCurveChart W 2) ≫
      integralCurveStructure W)
  (hα : Spec.map (CommRingCat.ofHom (α.comp (WeierstrassDilatation.fromOriginal W s
      (π * b3) (π * b4) (π ^ 2 * b6) h3 h4 h6)).toRingHom) ≫ integralCurveChart W 2 =
    leftSmoothPointAddition W p
      (Spec.map (CommRingCat.ofHom (β.comp (WeierstrassDilatation.fromOriginal W s
      (π * b3) (π * b4) (π ^ 2 * b6) h3 h4 h6)).toRingHom) ≫ integralCurveChart W 2) hp)

variable (hs : IsRegular (algebraMap R S s))
  (f : WeierstrassDilatation.Coordinate W s (π * b3) (π * b4) (π ^ 2 * b6))
  (hf : f ∈ modificationCenter W s π b3 b4 b6)
  (ψ : BlowupFractionChart.chart (modificationCenter W s π b3 b4 b6) f →+* S)
  (hβ : β.toRingHom = ψ.comp (algebraMap _ _))
  (hflat : RingHom.Flat ψ)
local notation "I" => modificationCenter W s π b3 b4 b6
local notation "den" => ψ (BlowupFractionChart.denominator I f)

variable [IsDomain R] (hπ : π ≠ 0)

/-- The constructed affine action lift into the actual local successor modification. -/
def successiveLocalAction : Spec (.of S) ⟶ modification W s π b3 b4 b6 :=
  successiveFractionActionToRees W s π b3 b4 b6 h3 h4 h6 p α β hp hα hs f hf ψ hβ hflat ≫
    (WeierstrassSuccessiveRees.modificationProjIso W s π b3 b4 b6 hπ).inv

/-- The whole local successor lift contracts to the prescribed divided output. -/
@[reassoc] theorem successiveLocalAction_contraction :
    successiveLocalAction W s π b3 b4 b6 h3 h4 h6 p α β hp hα hs f hf ψ hβ hflat hπ ≫
        contraction W s π b3 b4 b6 = Spec.map (CommRingCat.ofHom α.toRingHom) := by
  rw [successiveLocalAction, Category.assoc,
    ← WeierstrassSuccessiveRees.modificationProjIso_contraction W s π b3 b4 b6 hπ,
    Iso.inv_hom_id_assoc, successiveFractionActionToRees_contraction]

include hp hα hs hf hβ hflat hπ in
/-- Regular principalization separates all lifts over the actual preceding equation chart. -/
theorem successiveLocalAction_ext
    (a b : Spec (.of S) ⟶ modification W s π b3 b4 b6)
    (ha : a ≫ contraction W s π b3 b4 b6 = Spec.map (CommRingCat.ofHom α.toRingHom))
    (hb : b ≫ contraction W s π b3 b4 b6 = Spec.map (CommRingCat.ofHom α.toRingHom)) : a = b := by
  let _ := WeierstrassSuccessiveRees.contraction_isProper W s π b3 b4 b6 hπ
  apply RegularCenter.separated_lift_ext I α.toRingHom den
    (successiveFractionAction_principal W s π b3 b4 b6 h3 h4 h6 p α β hp hα hs f hf ψ hβ)
    (successiveFractionAction_denominator_regular W s π b3 b4 b6 f ψ hflat)
    (WeierstrassSuccessiveRees.centerGenerators W s π b3 b4 b6)
    (WeierstrassSuccessiveRees.centerGenerators_mem W s π b3 b4 b6)
    (WeierstrassSuccessiveRees.centerGenerators_span W s π b3 b4 b6)
    (contraction W s π b3 b4 b6) (𝟙 _) _ _ a b
  · simpa only [Category.comp_id] using ha
  · simpa only [Category.comp_id] using hb
  · intro i
    exact WeierstrassSuccessiveRees.originalOpen W s π b3 b4 b6 hπ
      (WeierstrassSuccessiveRees.centerGenerators W s π b3 b4 b6 i)
      (WeierstrassSuccessiveRees.centerGenerators_mem W s π b3 b4 b6 i)
  · intro i
    simpa only [Category.comp_id] using
      WeierstrassSuccessiveRees.originalOpen_isPullback W s π b3 b4 b6 hπ
        (WeierstrassSuccessiveRees.centerGenerators W s π b3 b4 b6 i)
        (WeierstrassSuccessiveRees.centerGenerators_mem W s π b3 b4 b6 i)

/-- The local action is characterized by its actual divided contraction. -/
theorem successiveLocalAction_unique
    (a : Spec (.of S) ⟶ modification W s π b3 b4 b6)
    (ha : a ≫ contraction W s π b3 b4 b6 = Spec.map (CommRingCat.ofHom α.toRingHom)) :
    a = successiveLocalAction W s π b3 b4 b6 h3 h4 h6 p α β hp hα hs f hf ψ hβ hflat hπ :=
  successiveLocalAction_ext W s π b3 b4 b6 h3 h4 h6 p α β hp hα hs f hf ψ hβ hflat hπ a _ ha
    (successiveLocalAction_contraction W s π b3 b4 b6 h3 h4 h6 p α β hp hα hs f hf ψ hβ hflat hπ)

end FLT.Mazur.WeierstrassSuccessiveX
