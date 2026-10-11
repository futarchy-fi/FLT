/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassLeftSmoothFractionActionGluing
public import FLT.Mazur.WeierstrassGlobalModificationActionPoints

/-!
# Integral fraction lifts agree with the global modification action

The comparison is made before residue specialization, using the regular
principal output center. Both original fraction inclusions are retained.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassIntegralChart
open WeierstrassGlobalModification WeierstrassModificationReesCoordinates
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R S : Type u} [CommRing R] [IsDomain R] [IsBezout R] [CommRing S]
  (W : WeierstrassCurve R) (s b3 b4 b6 : R)
  (h3 : W.a₃ = s * b3) (h4 : W.a₄ = s * b4) (h6 : W.a₆ = s ^ 2 * b6) (hs : s ≠ 0)
  (p : Spec (.of S) ⟶ (integralSmoothOpen W).toScheme) (α β : Coordinate W 2 →+* S)
  (hp : p ≫ integralSmoothStructure W =
    (Spec.map (CommRingCat.ofHom β) ≫ integralCurveChart W 2) ≫ integralCurveStructure W)
  (hα : Spec.map (CommRingCat.ofHom α) ≫ integralCurveChart W 2 =
    leftSmoothPointAddition W p (Spec.map (CommRingCat.ofHom β) ≫ integralCurveChart W 2) hp)
  (f : Coordinate W 2) (hf : f ∈ modificationChartCenter W s 2)
  (ψ : BlowupFractionChart.chart (modificationChartCenter W s 2) f →+* S)
  (hβ : β = ψ.comp (algebraMap (Coordinate W 2)
    (BlowupFractionChart.chart (modificationChartCenter W s 2) f)))
  (hflat : RingHom.Flat ψ)
local notation "h6'" => Eq.trans h6
  (Eq.trans (congrArg (· * b6) (pow_two s)) (mul_assoc s s b6))
local notation "J" => Iso.inv (modificationProjIso W s b3 b4 b6 h3 h4 h6 hs) ≫
  localChart W s b3 b4 b6 h3 h4 h6 hs
local notation "I" => BlowupRees.fractionChartInclusion (modificationChartCenter W s 2) f hf
local notation "b" => Spec.map (CommRingCat.ofHom ψ) ≫ I ≫ J
local notation "L" => leftSmoothFractionActionToRees W s b3 b4 (s * b6)
  h3 h4 h6' p α β hp hα f hf ψ hβ hflat

include hβ in
/-- The integral fraction input retains its original projective contraction. -/
theorem fractionActionGlobalInput_contraction :
    b ≫ contraction W s b3 b4 b6 h3 h4 h6 hs =
      Spec.map (CommRingCat.ofHom β) ≫ integralCurveChart W 2 := by
  simp only [Category.assoc, localChart_contraction, modificationProjIso_inv_contraction]
  change Spec.map (CommRingCat.ofHom ψ) ≫
    I ≫ BlowupRees.contraction (modificationChartCenter W s 2) ≫ integralCurveChart W 2 = _
  rw [BlowupRees.fractionChartInclusion_contraction_assoc, hβ,
    CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc]

include hp hβ in
/-- The actual smooth input and original fraction input have the same coefficient point. -/
theorem fractionActionGlobalInput_structure :
    p ≫ integralSmoothStructure W = b ≫ structureMap W s b3 b4 b6 h3 h4 h6 hs := by
  exact hp.trans (congrArg (· ≫ integralCurveStructure W)
    (fractionActionGlobalInput_contraction W s b3 b4 b6
      h3 h4 h6 hs β f hf ψ hβ).symm)

local notation "hb" => fractionActionGlobalInput_structure W s b3 b4 b6
  h3 h4 h6 hs p β hp f hf ψ hβ

/-- The glued affine fraction lift is the restriction of the actual global action. -/
theorem leftSmoothFractionActionToRees_global :
    L ≫ J = smoothPointAction W s b3 b4 b6 h3 h4 h6 hs p b hb := by
  apply regular_center_lift_ext W s b3 b4 b6 h3 h4 h6 hs α
    (ψ (BlowupFractionChart.denominator (modificationChartCenter W s 2) f))
    (leftSmoothFractionAction_principal W s b3 b4 (s * b6)
      h3 h4 h6' p α β hp hα f hf ψ hβ)
    (flatRingHom_isRegular ψ hflat
      (BlowupFractionChart.denominator_regular (modificationChartCenter W s 2) f))
  · simp only [Category.assoc, localChart_contraction, modificationProjIso_inv_contraction]
    exact leftSmoothFractionActionToRees_contraction_assoc W s b3 b4 (s * b6)
      h3 h4 h6' p α β hp hα f hf ψ hβ hflat (integralCurveChart W 2)
  · rw [smoothPointAction_contraction]
    simpa only [fractionActionGlobalInput_contraction W s b3 b4 b6
      h3 h4 h6 hs β f hf ψ hβ] using hα.symm

local notation "C" => leftSmoothFractionActionCover W s b3 b4 (s * b6)
  h3 h4 h6' p α β hp hα f hf ψ hβ hflat
local notation "M" => leftSmoothFractionActionLift W s b3 b4 (s * b6)
  h3 h4 h6' p α β hp hα f hf ψ hβ hflat

/-- Every original output fraction lift, including the horizontal one, is the global action. -/
theorem leftSmoothFractionActionLift_global (i : Fin 3) :
    Spec.map (CommRingCat.ofHom (M i)) ≫
        originalFractionCoverMap W s b3 b4 b6 h3 h4 h6 hs (some i) =
      smoothPointAction W s b3 b4 b6 h3 h4 h6 hs ((C).f i ≫ p) ((C).f i ≫ b)
        (by simpa only [Category.assoc] using congrArg ((C).f i ≫ ·) hb) := by
  have h := congrArg ((C).f i ≫ ·)
    (leftSmoothFractionActionToRees_global W s b3 b4 b6
      h3 h4 h6 hs p α β hp hα f hf ψ hβ hflat)
  rw [← Category.assoc, leftSmoothFractionActionCover_toRees] at h
  exact h.trans (smoothPointAction_comp W s b3 b4 b6 h3 h4 h6 hs
    ((C).f i) p b hb).symm


end FLT.Mazur.WeierstrassIntegralChart
