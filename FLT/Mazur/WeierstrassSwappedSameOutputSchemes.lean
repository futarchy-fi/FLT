/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSwappedAdditionIntersections

/-!
# Scheme comparisons on reversed-input addition intersections

Algebraic output comparisons on the actual tensor pullback extend to arbitrary
common schemes. This gives both same-family swapped addition identities.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.WeierstrassIntegralChart

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u

variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

/-- Algebraic equality on the concrete intersection implies equality on any common scheme. -/
theorem swappedAddition_compare (i j : AdditionChartIndex)
    {T : Type u} [CommRing T] [Algebra R T]
    (a : T →ₐ[R] additionChartRing W i) (b : T →ₐ[R] additionChartRing W j)
    (hab : (swappedAdditionLeft W i j).comp a =
      (swappedAdditionRight W i j).comp b)
    {X : Scheme} (f : X ⟶ Spec (additionChartRing W i))
    (g : X ⟶ Spec (additionChartRing W j))
    (hfg : f ≫ additionChartInclusion W i = g ≫ additionChartInclusion W j ≫ affineInputSwap W) :
    f ≫ Spec.map (CommRingCat.ofHom a.toRingHom) =
      g ≫ Spec.map (CommRingCat.ofHom b.toRingHom) := by
  have he : Spec.map (CommRingCat.ofHom (swappedAdditionLeft W i j).toRingHom) ≫
        Spec.map (CommRingCat.ofHom a.toRingHom) =
      Spec.map (CommRingCat.ofHom (swappedAdditionRight W i j).toRingHom) ≫
        Spec.map (CommRingCat.ofHom b.toRingHom) := by
    rw [← Spec.map_comp, ← Spec.map_comp]
    exact congrArg (fun h => Spec.map (CommRingCat.ofHom h.toRingHom)) hab
  have hp := swappedAddition_isPullback W i j
  have h := congrArg (fun k => hp.lift f g (by simpa only [Category.assoc] using hfg) ≫ k) he
  simpa only [← Category.assoc, hp.lift_fst, hp.lift_snd] using h

/-- Reversing inputs preserves every pair of ordinary output maps on common schemes. -/
theorem ordinaryAddition_swap_commonScheme (b c : Bool) {X : Scheme}
    (f : X ⟶ Spec (additionChartRing W (ordinaryIndex b)))
    (g : X ⟶ Spec (additionChartRing W (ordinaryIndex c)))
    (hfg : f ≫ additionChartInclusion W (ordinaryIndex b) =
      g ≫ additionChartInclusion W (ordinaryIndex c) ≫ affineInputSwap W) :
    f ≫ Spec.map (CommRingCat.ofHom (ordinaryChartAddition W b).toRingHom) =
      g ≫ Spec.map (CommRingCat.ofHom (ordinaryChartAddition W c).toRingHom) := by
  apply swappedAddition_compare W (ordinaryIndex b) (ordinaryIndex c)
    (ordinaryChartAddition W b) (ordinaryChartAddition W c) _ f g hfg
  exact ordinaryChartAddition_swap W b c _ _ (swappedAddition_inputs W _ _)

/-- Reversing inputs preserves every pair of reciprocal output maps on common schemes. -/
theorem reciprocalAddition_swap_commonScheme (b c : Bool) {X : Scheme}
    (f : X ⟶ Spec (additionChartRing W (reciprocalIndex b)))
    (g : X ⟶ Spec (additionChartRing W (reciprocalIndex c)))
    (hfg : f ≫ additionChartInclusion W (reciprocalIndex b) =
      g ≫ additionChartInclusion W (reciprocalIndex c) ≫ affineInputSwap W) :
    f ≫ Spec.map (CommRingCat.ofHom (reciprocalChartAddition W b).toRingHom) =
      g ≫ Spec.map (CommRingCat.ofHom (reciprocalChartAddition W c).toRingHom) := by
  apply swappedAddition_compare W (reciprocalIndex b) (reciprocalIndex c)
    (reciprocalChartAddition W b) (reciprocalChartAddition W c) _ f g hfg
  exact reciprocalChartAddition_swap W b c _ _ (swappedAddition_inputs W _ _)

end FLT.Mazur.WeierstrassIntegralChart
