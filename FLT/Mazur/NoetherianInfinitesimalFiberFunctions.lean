/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ArtinianProperRelativeFunctions
public import Mathlib.RingTheory.HopkinsLevitzki
public import Mathlib.RingTheory.Ideal.GoingUp

/-!
# Actual functions on infinitesimal closed fibers

Every maximal-ideal-power quotient of a Noetherian ring is Artinian. Applying
the proved Artinian-family theorem to the original scheme fiber product shows
that evaluation-zero functions vanish on every infinitesimal closed fiber.
Detecting their vanishing back on the original family is a separate next step.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry CategoryTheory.Limits
namespace FLT.Mazur.NoetherianInfinitesimalFiberFunctions
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-- All maximal-ideal-power quotients of a Noetherian ring are Artinian. -/
lemma quotient_pow_artinian {R : Type} [CommRing R] [IsNoetherianRing R]
    (I : Ideal R) [hI : I.IsMaximal] (n : ℕ) : IsArtinianRing (R ⧸ I ^ n) := by
  let _ : Ring.KrullDimLE 0 (R ⧸ I ^ n) := Ring.krullDimLE_zero_iff.mpr fun J hJ ↦ by
    let _ := hJ
    let _ := hJ.comap (Ideal.Quotient.mk (I ^ n))
    have hle : I ^ n ≤ J.comap (Ideal.Quotient.mk (I ^ n)) := by
      simpa only [Ideal.mk_ker] using
        (Ideal.ker_le_comap (Ideal.Quotient.mk (I ^ n)) :
          RingHom.ker _ ≤ J.comap (Ideal.Quotient.mk (I ^ n)))
    have he := hI.eq_of_le (Ideal.IsPrime.ne_top') (Ideal.IsPrime.le_of_pow_le hle)
    apply Ideal.isMaximal_of_isIntegral_of_isMaximal_under (R := R) J
    change (J.comap (Ideal.Quotient.mk (I ^ n))).IsMaximal
    rw [← he]
    exact hI
  exact IsNoetherianRing.isArtinianRing_of_krullDimLE_zero

/-- A fiber comparison kills the pullback of every original evaluation-zero function. -/
lemma pullback_eq_zero_of_bijective {X S T : Scheme.{0}} (f : X ⟶ S)
    (s : S ⟶ X) (hs : s ≫ f = 𝟙 S) (a : T ⟶ S)
    (H : Function.Bijective (pullback.snd f a).appTop)
    (x : Γ(X, ⊤)) (hx : s.appTop x = 0) :
    (pullback.fst f a).appTop x = 0 := by
  let t := SchemeProperGeometricFiberSections.baseChangedSection f s hs a
  have ht : t ≫ pullback.snd f a = 𝟙 _ :=
    SchemeProperGeometricFiberSections.baseChangedSection_projection f s hs a
  have ht' : t ≫ pullback.fst f a = a ≫ s := pullback.lift_fst _ _ _
  have hz : t.appTop ((pullback.fst f a).appTop x) = 0 := by
    change ((pullback.fst f a).appTop ≫ t.appTop) x = 0
    rw [← Scheme.Hom.comp_appTop, ht', Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
      hx, map_zero]
  obtain ⟨b, hb⟩ := H.surjective
    ((pullback.fst f a).appTop x)
  have he := SchemeRelativeNilpotentSections.evaluation_pullback (pullback.snd f a) t ht b
  rw [hb, hz] at he
  rw [← hb, ← he, map_zero]


variable {X S : Scheme.{0}} (f : X ⟶ S) [IsAffine S] [IsNoetherianRing Γ(S, ⊤)]
  [IsProper f] [Flat f] [GeometricallyConnected f] [GeometricallyReduced f]
  (s : S ⟶ X) (hs : s ≫ f = 𝟙 S)
  (I : Ideal Γ(S, ⊤)) [I.IsMaximal] (n : ℕ)

/-- The actual closed infinitesimal base defined by a maximal-ideal power. -/
def thickeningMap : Spec (.of (Γ(S, ⊤) ⧸ I ^ n)) ⟶ S :=
  AffineBaseChangeCoefficients.baseMap S (Γ(S, ⊤) ⧸ I ^ n)

attribute [irreducible] thickeningMap

include s hs in
/-- The actual infinitesimal fiber has precisely the functions on its infinitesimal base. -/
theorem appTop_bijective :
    Function.Bijective (pullback.snd f (thickeningMap I n)).appTop := by
  let _ := quotient_pow_artinian I n
  let _ : IsArtinianRing Γ(Spec (.of (Γ(S, ⊤) ⧸ I ^ n)), ⊤) :=
    (Scheme.ΓSpecIso (.of (Γ(S, ⊤) ⧸ I ^ n))).symm.commRingCatIsoToRingEquiv.isArtinianRing
  exact ArtinianProperRelativeFunctions.appTop_bijective _
    (SchemeProperGeometricFiberSections.baseChangedSection f s hs (thickeningMap I n))
    (SchemeProperGeometricFiberSections.baseChangedSection_projection f s hs (thickeningMap I n))

include hs in
/-- Evaluation-zero original functions vanish on every actual infinitesimal closed fiber. -/
theorem pullback_eq_zero (x : Γ(X, ⊤)) (hx : s.appTop x = 0) :
    (pullback.fst f (thickeningMap I n)).appTop x = 0 :=
  pullback_eq_zero_of_bijective f s hs (thickeningMap I n)
    (appTop_bijective f s hs I n) x hx

end FLT.Mazur.NoetherianInfinitesimalFiberFunctions
