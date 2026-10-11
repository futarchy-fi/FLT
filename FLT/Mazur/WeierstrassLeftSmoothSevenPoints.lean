/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassLeftSmoothAdditionOutputRegular
public import FLT.Mazur.WeierstrassFiniteChartDescent

/-!
# The seven actual points for integral action associativity

The three inputs, two intermediate sums and two final outputs form an actual
family on the smooth by smooth by whole cubic product. Every one of the first
five Z coordinates is regular on a flat simultaneous chart presentation.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

/-- The three original points, both intermediate sums and both iterated sums. -/
def leftSmoothTripleSevenPoint : Fin 7 → (leftSmoothTriple W ⟶ integralCurve W) :=
  ![leftSmoothTripleFirst W ≫ (integralSmoothOpen W).ι,
    leftSmoothTripleSecond W ≫ (integralSmoothOpen W).ι,
    leftSmoothTripleThird W,
    leftSmoothTriplePair W ≫ smoothFactorAddition W ≫ (integralSmoothOpen W).ι,
    leftSmoothTripleLastPair W ≫ leftSmoothFactorAddition W,
    leftSmoothTripleAddLeft W,
    leftSmoothTripleAddRight W]

/-- The three inputs and both intermediate sums have regular Z on every flat chart. -/
theorem leftSmoothTripleSevenPoint_z_regular {X : Scheme.{u}}
    (t : X ⟶ leftSmoothTriple W) [Flat t] (b : Fin 7 → Bool)
    (p : (i : Fin 7) → X ⟶ chartScheme W (productChartCoordinate (b i)))
    (hp : ∀ i, p i ≫ integralCurveChart W (productChartCoordinate (b i)) =
      t ≫ leftSmoothTripleSevenPoint W i) (i : Fin 5) :
    IsRegular (specSectionHom (p (i.castAdd 2))
      (coord W (productChartCoordinate (b (i.castAdd 2))) 2)) := by
  fin_cases i
  · exact leftSmoothTripleFirst_z_regular W t (b 0) (p 0) (hp 0)
  · exact leftSmoothTripleSecond_z_regular W t (b 1) (p 1) (hp 1)
  · exact leftSmoothTripleThird_z_regular W t (b 2) (p 2) (hp 2)
  · exact leftSmoothTripleFirstSum_z_regular W t (b 3) (p 3) (hp 3)
  · exact leftSmoothTripleLastSum_z_regular W t (b 4) (p 4) (hp 4)

/-- Simultaneous charts reduce actual iterated-sum equality to flat affine sources. -/
theorem leftSmoothTripleAdd_eq_of_chart_tests
    (h : ∀ {S : Type u} [CommRing S] (t : Spec (.of S) ⟶ leftSmoothTriple W),
      Flat t → ∀ (b : Fin 7 → Bool)
        (p : (i : Fin 7) → Spec (.of S) ⟶ chartScheme W (productChartCoordinate (b i))),
        (∀ i, p i ≫ integralCurveChart W (productChartCoordinate (b i)) =
          t ≫ leftSmoothTripleSevenPoint W i) →
        t ≫ leftSmoothTripleAddLeft W = t ≫ leftSmoothTripleAddRight W) :
    leftSmoothTripleAddLeft W = leftSmoothTripleAddRight W := by
  apply finiteCurveCharts_hom_ext W 7 (leftSmoothTripleSevenPoint W)
  intro X t ht b p hp
  let _ := ht
  apply Scheme.Cover.hom_ext X.affineCover
  intro i
  let a := X.affineCover.f i
  have he : ∀ j, (a ≫ p j) ≫ integralCurveChart W (productChartCoordinate (b j)) =
      (a ≫ t) ≫ leftSmoothTripleSevenPoint W j := by
    intro j
    rw [Category.assoc, hp, Category.assoc]
  simpa only [Category.assoc] using h (a ≫ t) inferInstance b (fun j => a ≫ p j) he

end FLT.Mazur.WeierstrassIntegralChart
