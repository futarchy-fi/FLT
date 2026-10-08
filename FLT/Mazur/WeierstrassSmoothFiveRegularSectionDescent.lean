/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSmoothFiveRegularChartDescent
public import FLT.Mazur.WeierstrassFiveRegularSectionDescent

/-!
# Five-regular descent using scheme presentations

Convert chart morphisms on an affine spectrum into their actual ring maps.
The resulting associativity criterion takes the global sections supplied by
flat chart and addition projections directly.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
variable {R S A : Type u} [CommRing R] [CommRing S]

variable (W : WeierstrassCurve R)

/-- Five regular chart sections imply associativity on any explicit affine spectrum. -/
theorem smoothFactorTripleAdd_of_fiveRegularSections
    (t : Spec (.of S) ⟶ smoothFactorTriple W) (j : Fin 5 → Fin 3)
    (p : (i : Fin 5) → Spec (.of S) ⟶ chartScheme W (j i))
    (hp : ∀ i, p i ≫ integralCurveChart W (j i) = smoothTripleFivePoint W t i)
    (hz : ∀ i, IsRegular (specSectionHom (p i) (coord W (j i) 2))) (c e : Fin 3)
    (l : Spec (.of S) ⟶ chartScheme W c) (r : Spec (.of S) ⟶ chartScheme W e)
    (hl : l ≫ integralCurveChart W c =
      t ≫ smoothFactorTripleAddLeft W ≫ (integralSmoothOpen W).ι)
    (hr : r ≫ integralCurveChart W e =
      t ≫ smoothFactorTripleAddRight W ≫ (integralSmoothOpen W).ι) :
    t ≫ smoothFactorTripleAddLeft W =
      t ≫ smoothFactorTripleAddRight W := by
  apply smoothFactorTripleAdd_of_fiveRegularCharts W t j
    (fun i => affineChartRingHom (p i))
    (fun i => by rw [affineChartRingHom_spec]; exact hp i)
    (fun i => affineChartRingHom_isRegular (p i) (hz i)) c e
    (affineChartRingHom l) (affineChartRingHom r)
  · simpa only [affineChartRingHom_spec] using hl
  · simpa only [affineChartRingHom_spec] using hr

end FLT.Mazur.WeierstrassIntegralChart
