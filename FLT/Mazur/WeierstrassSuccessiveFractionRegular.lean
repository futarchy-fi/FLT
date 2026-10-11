/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSuccessiveFractionAction

/-!
# Regular scales on actual successor fraction presentations

The original divided chart is flat over the coefficients. Its fraction
algebra embeds in a principal localization, so every regular coefficient
remains regular there and on flat affine smooth-input presentations.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.WeierstrassSuccessiveX
open WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type*} [CommRing R]
  (W : WeierstrassCurve R) (s π b3 b4 b6 : R)
local notation "B" =>
  WeierstrassDilatation.Coordinate W s (π * b3) (π * b4) (π ^ 2 * b6)
variable (f : WeierstrassDilatation.Coordinate W s (π * b3) (π * b4) (π ^ 2 * b6))
local notation "I" => modificationCenter W s π b3 b4 b6
local notation "C" => BlowupFractionChart.chart I f

/-- Every regular coefficient survives in every actual successor fraction chart. -/
theorem successiveFraction_coefficient_regular {r : R} (hr : IsRegular r) :
    IsRegular (algebraMap B C (algebraMap R B r)) := by
  have hB := flatRingHom_isRegular (algebraMap R B)
    (RingHom.flat_algebraMap_iff.mpr inferInstance) hr
  have hL := flatRingHom_isRegular (algebraMap B (Localization.Away f))
    (RingHom.flat_algebraMap_iff.mpr (IsLocalization.flat _ (Submonoid.powers f))) hB
  constructor
  · intro a b he
    apply Subtype.ext
    apply hL.left
    exact congrArg (fun z : C => (z : Localization.Away f)) he
  · intro a b he
    apply Subtype.ext
    apply hL.right
    exact congrArg (fun z : C => (z : Localization.Away f)) he

variable {S : Type*} [CommRing S] [Algebra R S]
  (β : WeierstrassDilatation.Coordinate W s (π * b3) (π * b4) (π ^ 2 * b6) →ₐ[R] S)
  (ψ : BlowupFractionChart.chart (modificationCenter W s π b3 b4 b6) f →+* S)
  (hβ : β.toRingHom = ψ.comp (algebraMap _ _)) (hflat : RingHom.Flat ψ)

include hβ hflat in
/-- The scale is regular on a flat smooth-input presentation of a successor fraction chart. -/
theorem successiveFractionPresentation_scale_regular (hs : IsRegular s) :
    IsRegular (algebraMap R S s) := by
  have h := flatRingHom_isRegular ψ hflat
    (successiveFraction_coefficient_regular W s π b3 b4 b6 f hs)
  have he : ψ (algebraMap B C (algebraMap R B s)) = algebraMap R S s := by
    have he := RingHom.congr_fun hβ (algebraMap R B s)
    exact he.symm.trans (β.commutes s)
  rwa [he] at h

end FLT.Mazur.WeierstrassSuccessiveX
