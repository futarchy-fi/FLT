/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSmoothAdditionOutputRegular
public import FLT.Mazur.WeierstrassSmoothFiveRegularSectionDescent

/-!
# Seven actual points for full smooth associativity descent

The three inputs, two intermediate sums and two final outputs form the
finite family used in simultaneous chart descent. The first five have regular
Z on every flat Y/Z presentation, by the proved local formula calculations.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

/-- The five original and intermediate points followed by the two actual iterated sums. -/
def smoothTripleSevenPoint : Fin 7 → (smoothFactorTriple W ⟶ integralCurve W) :=
  ![smoothFactorTripleFirst W ≫ (integralSmoothOpen W).ι,
    smoothFactorTripleSecond W ≫ (integralSmoothOpen W).ι,
    smoothFactorTripleThird W ≫ (integralSmoothOpen W).ι,
    smoothFactorTriplePair W ≫ smoothFactorAddition W ≫ (integralSmoothOpen W).ι,
    smoothFactorTripleLastPair W ≫ smoothFactorAddition W ≫ (integralSmoothOpen W).ι,
    smoothFactorTripleAddLeft W ≫ (integralSmoothOpen W).ι,
    smoothFactorTripleAddRight W ≫ (integralSmoothOpen W).ι]

/-- The first five members retain the previously selected input and intermediate points. -/
theorem smoothTripleSevenPoint_firstFive {X : Scheme.{u}} (t : X ⟶ smoothFactorTriple W)
    (i : Fin 5) : t ≫ smoothTripleSevenPoint W (i.castAdd 2) = smoothTripleFivePoint W t i := by
  fin_cases i <;> simp [smoothTripleSevenPoint, smoothTripleFivePoint]

/-- Every one of the five required coordinates is regular on a flat simultaneous chart. -/
theorem smoothTripleSevenPoint_z_regular {X : Scheme.{u}}
    (t : X ⟶ smoothFactorTriple W) [Flat t] (b : Fin 7 → Bool)
    (p : (i : Fin 7) → X ⟶ chartScheme W (productChartCoordinate (b i)))
    (hp : ∀ i, p i ≫ integralCurveChart W (productChartCoordinate (b i)) =
      t ≫ smoothTripleSevenPoint W i) (i : Fin 5) :
    IsRegular (specSectionHom (p (i.castAdd 2))
      (coord W (productChartCoordinate (b (i.castAdd 2))) 2)) := by
  fin_cases i
  · exact smoothTripleFirst_z_regular W t (b 0) (p 0) (hp 0)
  · exact smoothTripleSecond_z_regular W t (b 1) (p 1) (hp 1)
  · exact smoothTripleThird_z_regular W t (b 2) (p 2) (hp 2)
  · exact smoothTripleFirstSum_z_regular W t (b 3) (p 3) (hp 3)
  · exact smoothTripleLastSum_z_regular W t (b 4) (p 4) (hp 4)

/-- Seven chart presentations on a flat affine source give equality of the actual smooth sums. -/
theorem smoothFactorTripleAdd_of_sevenCharts {S : Type u} [CommRing S]
    (t : Spec (.of S) ⟶ smoothFactorTriple W) [Flat t] (b : Fin 7 → Bool)
    (p : (i : Fin 7) → Spec (.of S) ⟶ chartScheme W (productChartCoordinate (b i)))
    (hp : ∀ i, p i ≫ integralCurveChart W (productChartCoordinate (b i)) =
      t ≫ smoothTripleSevenPoint W i) :
    t ≫ smoothFactorTripleAddLeft W = t ≫ smoothFactorTripleAddRight W := by
  apply smoothFactorTripleAdd_of_fiveRegularSections W t
    (fun i => productChartCoordinate (b (i.castAdd 2))) (fun i => p (i.castAdd 2))
    (fun i => (hp _).trans (smoothTripleSevenPoint_firstFive W t i))
    (smoothTripleSevenPoint_z_regular W t b p hp)
    (productChartCoordinate (b 5)) (productChartCoordinate (b 6)) (p 5) (p 6)
  · exact hp 5
  · exact hp 6

end FLT.Mazur.WeierstrassIntegralChart
