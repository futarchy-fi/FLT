/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSplitNormalizationInfinityParameter

/-!
# Original infinity parameters agree with every full punctured slope map

Equality after the actual cubic inclusion determines the infinity parameter
on any source mapping to the complete two-root slope open.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur
open WeierstrassIntegralChart ProjectiveLine WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {K : Type u} [Field K] (W : WeierstrassCurve K) (a : Kˣ)
  (he : W = splitNodalEquation a)
  (h₂ : W.a₂ = 0) (h₃ : W.a₃ = 0) (h₄ : W.a₄ = 0) (h₆ : W.a₆ = 0)
local notation "s" => PrincipalOpenTransport.inclusion (slopePolynomial (a : K))

/-- The full original infinity parameter is fixed by its entire punctured affine restriction. -/
theorem splitEquationInfinityParameter_slope {X : Scheme.{u}}
    (f : X ⟶ Spec (.of (SlopeOpen (a : K)))) (g : X ⟶ chartScheme W 1)
    (h : g ≫ integralCurveChart W 1 =
      f ≫ s ≫ splitAffineToCubic W h₂ h₃ h₄ h₆) :
    g ≫ splitEquationInfinityParameter W a he = f ≫ s ≫ left K := by
  subst W
  let m := Spec.map (CommRingCat.ofHom (slopeLaurentMap a).toRingHom)
  have hg : g = f ≫ m ≫ (splitNodalTorusIso a).hom := by
    apply (cancel_mono (integralCurveChart (splitNodalEquation a) 1)).mp
    rw [h, splitNormalization_slope_overlap]
    rfl
  rw [hg]
  change (f ≫ m ≫ (splitNodalTorusIso a).hom) ≫
    (splitNodalTorusIso a).inv ≫ infinityTorusChart a = _
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [← infinityTorus_slope_condition]

end FLT.Mazur
