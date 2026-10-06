/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.EllipticCurve.CubicSecantRegular
public import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant

/-! # Uniqueness on schematically dense domains

These comparison results retain nilpotent coefficients. Topological density
alone would not justify equality of the scheme morphisms constructed here. -/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
set_option backward.isDefEq.respectTransparency false

namespace WeierstrassCurve.CubicCharts
universe u

/-- Maps into a separated relative scheme agree if they agree after a
scheme-theoretically dominant restriction. No reducedness hypothesis is needed. -/
theorem hom_ext_of_schematic_dominance {X Y Z U : Scheme.{u}} {f g : X ⟶ Y}
    (s : Y ⟶ Z) [IsSeparated s] (h : f ≫ s = g ≫ s)
    (ι : U ⟶ X) [IsSchemeTheoreticallyDominant ι] (hU : ι ≫ f = ι ≫ g) : f = g := by
  let X' : Over Z := Over.mk (f ≫ s)
  let Y' : Over Z := Over.mk s
  let U' : Over Z := Over.mk (ι ≫ f ≫ s)
  let f' : X' ⟶ Y' := Over.homMk f
  let g' : X' ⟶ Y' := Over.homMk g
  let ι' : U' ⟶ X' := Over.homMk ι
  have : IsSeparated Y'.hom := ‹_›
  have he : ι' ≫ f' = ι' ≫ g' := by ext1; exact hU
  have hi : (equalizer.lift ι' he).left ≫ (equalizer.ι f' g').left = ι := by
    rw [← Over.comp_left, equalizer.lift_ι]
    rfl
  have hk : (equalizer.ι f' g').left.ker = ⊥ := by
    apply le_antisymm
    · calc
        (equalizer.ι f' g').left.ker ≤
            ((equalizer.lift ι' he).left ≫ (equalizer.ι f' g').left).ker :=
          Scheme.Hom.le_ker_comp _ _
        _ = ⊥ := by rw [hi, ι.ker_eq_bot]
    · exact bot_le
  have : IsIso (equalizer.ι f' g').left :=
    IsClosedImmersion.isIso_iff_ker_eq_bot.mpr hk
  rw [← cancel_epi (equalizer.ι f' g').left]
  exact congr($(equalizer.condition f' g').left)

/-- An injective homomorphism of rings gives a scheme-theoretically dominant spectrum map. -/
theorem specMap_schematic_dominance {A B : Type u} [CommRing A] [CommRing B]
    (f : A →+* B) (hf : Function.Injective f) :
    IsSchemeTheoreticallyDominant (Spec.map (CommRingCat.ofHom f)) := by
  let φ := CommRingCat.ofHom f
  have : Mono φ := ConcreteCategory.mono_of_injective φ hf
  have : Mono ((Spec.map φ).appTop ≫ (Scheme.ΓSpecIso (.of B)).hom) := by
    rw [Scheme.ΓSpecIso_naturality]
    infer_instance
  have : Mono (Spec.map φ).appTop := mono_of_mono (Spec.map φ).appTop (Scheme.ΓSpecIso (.of B)).hom
  have hh : Function.Injective (Spec.map φ).appTop :=
    ConcreteCategory.injective_of_mono_of_preservesPullback _
  constructor
  exact Scheme.IdealSheafData.ext_of_isAffine (by
    simpa [Scheme.Hom.ker_apply, ← RingHom.injective_iff_ker_eq_bot] using hh)

/-- The secant domain is schematically dense in the affine input product over every base ring. -/
theorem secant_schematic_dominance {R : Type u} [CommRing R] (W : WeierstrassCurve R) :
    IsSchemeTheoreticallyDominant
      (Spec.map (CommRingCat.ofHom (algebraMap (AffinePairRing W) (SecantRing W)))) :=
  specMap_schematic_dominance _ (secantRestriction_injective W)

end WeierstrassCurve.CubicCharts
