/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedDepthCenterNormalization
public import FLT.Mazur.WeierstrassSuccessiveLocalAction
public import FLT.Mazur.WeierstrassSuccessiveFractionRegular
public import FLT.Mazur.WeierstrassDividedExteriorLocalContraction

/-!
# Local action lifts into the normalized exterior successor

A flat fraction-input presentation of the genuine smooth action lifts into
the actual local replacement at any divided depth. The existing reassociation
then puts it in the next exterior model with the exact step contraction.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] {W : WeierstrassCurve R} {π : R}
  {k : ℕ} (hπ : π ≠ 0) (d : Data W π k) (e : Data W π (k + 1))
local notation "B" => WeierstrassDilatation.Coordinate W (π ^ k)
  (π * e.b3) (π * e.b4) (π ^ 2 * e.b6)

/-- The normalized preceding chart's original affine-coordinate map. -/
def previousOriginalMap : Coordinate W 2 →ₐ[R] B :=
  WeierstrassDilatation.fromOriginal W (π ^ k) (π * e.b3) (π * e.b4) (π ^ 2 * e.b6)
    (by rw [← factor3_step hπ d e]; exact d.factor3)
    (by rw [← factor4_step hπ d e]; exact d.factor4)
    (by rw [← factor6_step hπ d e]; exact d.factor6)

variable {S : Type u} [CommRing S] [Algebra R S]
  (p : Spec (.of S) ⟶ (integralSmoothOpen W).toScheme)
  (α β : WeierstrassDilatation.Coordinate W (π ^ k)
    (π * e.b3) (π * e.b4) (π ^ 2 * e.b6) →ₐ[R] S)
  (hp : p ≫ integralSmoothStructure W =
    (Spec.map (CommRingCat.ofHom (β.comp (previousOriginalMap hπ d e)).toRingHom) ≫
      integralCurveChart W 2) ≫ integralCurveStructure W)
  (hα : Spec.map (CommRingCat.ofHom (α.comp (previousOriginalMap hπ d e)).toRingHom) ≫
    integralCurveChart W 2 = leftSmoothPointAddition W p
      (Spec.map (CommRingCat.ofHom (β.comp (previousOriginalMap hπ d e)).toRingHom) ≫
        integralCurveChart W 2) hp)
  (f : WeierstrassDilatation.Coordinate W (π ^ k)
    (π * e.b3) (π * e.b4) (π ^ 2 * e.b6))
  (hf : f ∈ WeierstrassSuccessiveX.modificationCenter W (π ^ k) π e.b3 e.b4 e.b6)
  (ψ : BlowupFractionChart.chart
    (WeierstrassSuccessiveX.modificationCenter W (π ^ k) π e.b3 e.b4 e.b6) f →+* S)
  (hβ : β.toRingHom = ψ.comp (algebraMap _ _)) (hflat : RingHom.Flat ψ)

/-- The actual normalized local lift; scale regularity is proved from the flat fraction input. -/
def depthLocalAction : Spec (.of S) ⟶ WeierstrassSuccessiveX.depthStep π k W e.b3 e.b4 e.b6 :=
  WeierstrassSuccessiveX.successiveLocalAction W (π ^ k) π e.b3 e.b4 e.b6
    (by rw [← factor3_step hπ d e]; exact d.factor3)
    (by rw [← factor4_step hπ d e]; exact d.factor4)
    (by rw [← factor6_step hπ d e]; exact d.factor6) p α β hp hα
    (WeierstrassSuccessiveX.successiveFractionPresentation_scale_regular
      W (π ^ k) π e.b3 e.b4 e.b6 f β ψ hβ hflat (IsRegular.of_ne_zero (pow_ne_zero k hπ)))
    f hf ψ hβ hflat hπ

/-- Contraction lands in the exact normalized preceding chart. -/
@[reassoc] theorem depthLocalAction_contraction :
    depthLocalAction hπ d e p α β hp hα f hf ψ hβ hflat ≫ localContraction hπ d e =
      Spec.map (CommRingCat.ofHom α.toRingHom) ≫ (previousChartIso hπ d e).hom := by
  change depthLocalAction hπ d e p α β hp hα f hf ψ hβ hflat ≫
    WeierstrassSuccessiveX.contraction W (π ^ k) π e.b3 e.b4 e.b6 ≫ _ = _
  rw [depthLocalAction, WeierstrassSuccessiveX.successiveLocalAction_contraction_assoc]
  rfl

/-- This local lift contracts all the way to the genuine original smooth action. -/
@[reassoc] theorem depthLocalAction_original :
    depthLocalAction hπ d e p α β hp hα f hf ψ hβ hflat ≫
        localContraction hπ d e ≫ toCurve d =
      leftSmoothPointAddition W p
        (Spec.map (CommRingCat.ofHom (β.comp (previousOriginalMap hπ d e)).toRingHom) ≫
          integralCurveChart W 2) hp := by
  rw [depthLocalAction_contraction_assoc, previousChartIso_toCurve]
  change Spec.map _ ≫ (Spec.map _ ≫ _) = _
  rw [← Category.assoc, ← Spec.map_comp]
  exact hα

variable (E : Exterior d)

/-- Insert the constructed lift into the actual advanced exterior model. -/
def Exterior.depthActionLift : Spec (.of S) ⟶ (E.advance hπ e).whole :=
  depthLocalAction hπ d e p α β hp hα f hf ψ hβ hflat ≫
    pushout.inr E.attach (localBoundary hπ d e) ≫ (E.advanceIso hπ e).inv

/-- The local successor action has exactly the existing whole step contraction. -/
@[reassoc] theorem Exterior.depthActionLift_step :
    E.depthActionLift hπ d e p α β hp hα f hf ψ hβ hflat ≫ E.stepContraction hπ e =
      Spec.map (CommRingCat.ofHom α.toRingHom) ≫
        (previousChartIso hπ d e).hom ≫ E.dividedChart := by
  rw [Exterior.depthActionLift, Category.assoc, Category.assoc,
    ← E.advanceIso_contraction hπ e, Iso.inv_hom_id_assoc,
    E.localReplacement_inr_contraction hπ e, depthLocalAction_contraction_assoc]

end FLT.Mazur.WeierstrassDividedDepth
