/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassAdditionSwapFormula
public import FLT.Mazur.WeierstrassInfinityAdditionScheme

/-!
# Commutativity on the polynomial addition domains

The opposite input order has the same principal output opens: the defining
coordinate changes only by minus one. Localizing the actual tensor swap
therefore compares the two normalized regular addition maps directly.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) (j k t : Fin 3)

/-- The swapped output coordinate is a unit on the original output open. -/
theorem additionOutputSwap_isUnit : IsUnit
    (((additionOutputRestriction W k j t).comp (chartProductSwap W j k))
      (chartProductAdditionCoordinates W j k t)) := by
  change IsUnit (additionOutputRestriction W k j t
    (chartProductSwap W j k (chartProductAdditionCoordinates W j k t)))
  rw [chartProductAdditionCoordinates_swap, map_neg]
  exact (additionOutput_isUnit W k j t).neg

/-- The actual input interchange extends to every polynomial output open. -/
def additionOutputSwap : AdditionOutputOpen W j k t →ₐ[R] AdditionOutputOpen W k j t :=
  IsLocalization.Away.liftAlgHom (chartProductAdditionCoordinates W j k t)
    (additionOutputSwap_isUnit W j k t)

/-- The localized swap retains the original input interchange. -/
@[simp] theorem additionOutputSwap_restriction (a : ChartProduct W j k) :
    additionOutputSwap W j k t (additionOutputRestriction W j k t a) =
      additionOutputRestriction W k j t (chartProductSwap W j k a) :=
  IsLocalization.Away.lift_eq _ (additionOutputSwap_isUnit W j k t) a

/-- Normalization cancels the common minus sign in the homogeneous output. -/
theorem projectiveAdditionChart_swap :
    (additionOutputSwap W j k t).comp (projectiveAdditionChart W j k t) =
      projectiveAdditionChart W k j t := by
  apply projectiveAdditionChart_comp_eq
  intro i
  simp only [additionOutputSwap_restriction, chartProductAdditionCoordinates_swap, map_neg]
  linear_combination -projectiveAdditionChart_mul W k j t i

/-- On schemes, the localized interchange lies over the tensor-product interchange. -/
theorem additionOutputSwap_inclusion :
    Spec.map (CommRingCat.ofHom (additionOutputSwap W j k t).toRingHom) ≫
        projectiveAdditionInclusion W j k t =
      projectiveAdditionInclusion W k j t ≫
        Spec.map (CommRingCat.ofHom (chartProductSwap W j k).toRingHom) := by
  change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  exact RingHom.ext (additionOutputSwap_restriction W j k t)

/-- The actual normalized polynomial addition morphisms agree after swapping inputs. -/
theorem projectiveAdditionSpec_swap :
    Spec.map (CommRingCat.ofHom (additionOutputSwap W j k t).toRingHom) ≫
        Spec.map (CommRingCat.ofHom (projectiveAdditionChart W j k t).toRingHom) =
      Spec.map (CommRingCat.ofHom (projectiveAdditionChart W k j t).toRingHom) := by
  rw [← Spec.map_comp]
  exact congrArg (fun f => Spec.map (CommRingCat.ofHom f.toRingHom))
    (projectiveAdditionChart_swap W j k t)

end FLT.Mazur.WeierstrassIntegralChart
