/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassPolynomialInputTransition
public import FLT.Mazur.WeierstrassIntegralCurveMorphisms
public import FLT.Mazur.WeierstrassInfinityAdditionScheme

/-!
# Polynomial addition on common schemes across input normalization

The concrete localization pullback lets the established polynomial comparison
apply to arbitrary schemes mapping into the simultaneous input overlap.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R) (j k j' k' t : Fin 3)

/-- The changed polynomial domain preserves the changed input-product map. -/
theorem inputPolynomialOther_inclusion :
    Spec.map (CommRingCat.ofHom (inputPolynomialOther W j k j' k' t).toRingHom) ≫
        projectiveAdditionInclusion W j' k' t =
      Spec.map (CommRingCat.ofHom (inputPolynomialRestriction W j k j' k' t).toRingHom) ≫
        Spec.map (CommRingCat.ofHom (productOverlapOther W j k j' k').toRingHom) := by
  change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  exact RingHom.ext (inputPolynomialOther_restriction W j k j' k' t)

/-- Polynomial laws with the same output chart agree across both input normalizations. -/
theorem polynomialInput_commonScheme {X : Scheme.{u}}
    (v : X ⟶ Spec (.of (ProductOverlap W j k j' k')))
    (f : X ⟶ Spec (.of (AdditionOutputOpen W j k t)))
    (g : X ⟶ Spec (.of (AdditionOutputOpen W j' k' t)))
    (hf : v ≫ Spec.map (CommRingCat.ofHom (productOverlapRestriction W j k j' k').toRingHom) =
      f ≫ projectiveAdditionInclusion W j k t)
    (hg : v ≫ Spec.map (CommRingCat.ofHom (productOverlapOther W j k j' k').toRingHom) =
      g ≫ projectiveAdditionInclusion W j' k' t) :
    f ≫ Spec.map (CommRingCat.ofHom (projectiveAdditionChart W j k t).toRingHom) =
      g ≫ Spec.map (CommRingCat.ofHom (projectiveAdditionChart W j' k' t).toRingHom) := by
  let l := (inputPolynomial_isPullback W j k j' k' t).lift v f hf
  have hl : l ≫ Spec.map (CommRingCat.ofHom
      (inputPolynomialOther W j k j' k' t).toRingHom) = g := by
    apply (cancel_mono (projectiveAdditionInclusion W j' k' t)).mp
    rw [Category.assoc, inputPolynomialOther_inclusion, ← Category.assoc,
      IsPullback.lift_fst]
    exact hg
  have he := congrArg (fun a => l ≫ a)
    (inputPolynomialAddition_spec W j k j' k' t).symm
  simpa only [← Category.assoc, hl, l, IsPullback.lift_snd] using he

/-- The same comparison holds for maps into the global integral cubic. -/
theorem polynomialInput_curve_eq {X : Scheme.{u}}
    (v : X ⟶ Spec (.of (ProductOverlap W j k j' k')))
    (f : X ⟶ Spec (.of (AdditionOutputOpen W j k t)))
    (g : X ⟶ Spec (.of (AdditionOutputOpen W j' k' t)))
    (hf : v ≫ Spec.map (CommRingCat.ofHom (productOverlapRestriction W j k j' k').toRingHom) =
      f ≫ projectiveAdditionInclusion W j k t)
    (hg : v ≫ Spec.map (CommRingCat.ofHom (productOverlapOther W j k j' k').toRingHom) =
      g ≫ projectiveAdditionInclusion W j' k' t) :
    (f ≫ Spec.map (CommRingCat.ofHom (projectiveAdditionChart W j k t).toRingHom)) ≫
        integralCurveChart W t =
      (g ≫ Spec.map (CommRingCat.ofHom (projectiveAdditionChart W j' k' t).toRingHom)) ≫
        integralCurveChart W t :=
  congrArg (fun a => a ≫ integralCurveChart W t)
    (polynomialInput_commonScheme W j k j' k' t v f g hf hg)

end FLT.Mazur.WeierstrassIntegralChart
