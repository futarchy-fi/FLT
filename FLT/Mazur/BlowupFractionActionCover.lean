/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.BlowupFractionRatioCover
public import FLT.Mazur.BlowupFractionRatioLift
public import Mathlib.AlgebraicGeometry.Cover.Open

/-!
# The complete input ratio cover for an invariant center

Equality of the pulled-back center with the input center gives a genuine open
cover of each input fraction chart by the output-generator ratios. On each
member there is an actual map to the corresponding original output chart.
The cover in this file is of the blowup of the extended ideal; identifying
it with a modified product requires the appropriate base-change comparison.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

namespace FLT.Mazur.BlowupFractionChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
variable {A B : Type u} [CommRing A] [CommRing B]
  (I : Ideal A) (J : Ideal B) (φ : A →+* B) (hφ : I.map φ = J)
  {ι : Type u} (g : ι → A) (hg : ∀ i, g i ∈ I)
  (hspan : Ideal.span (Set.range g) = I) (f : B) (hf : f ∈ J)

include hφ hspan in
/-- Images of the original generators span the entire input center, with nilpotents retained. -/
theorem image_generator_span : Ideal.span (Set.range fun i => φ (g i)) = J := by
  rw [Set.range_comp', ← Ideal.map_span, hspan, hφ]

/-- The actual affine ratio opens cover the entire input fraction chart. -/
def actionRatioCover : (Spec (.of (chart J f))).AffineOpenCover :=
  Scheme.affineOpenCoverOfSpanRangeEqTop
    (fun i => ratio J f (φ (g i)) (hφ.le (Ideal.mem_map_of_mem φ (hg i))))
    (ratio_span_eq_top J f (fun i => φ (g i))
      (fun i => hφ.le (Ideal.mem_map_of_mem φ (hg i)))
      (image_generator_span I J φ hφ g hspan) hf)

/-- The map from a real input ratio open to the matching original output fraction chart. -/
def actionRatioChartMap (i : ι) :
    Spec (.of (BlowupRees.FractionRatioOpen J f (φ (g i))
      (hφ.le (Ideal.mem_map_of_mem φ (hg i))))) ⟶ Spec (.of (chart I (g i))) :=
  Spec.map (CommRingCat.ofHom (ratioLift I J φ hφ.le f hf (g i) (hg i)))

/-- Every local action lift contracts to precisely the given original coefficient map. -/
@[reassoc] theorem actionRatioChartMap_contraction (i : ι) :
    actionRatioChartMap I J φ hφ g hg f hf i ≫
        Spec.map (CommRingCat.ofHom (algebraMap A (chart I (g i)))) =
      (actionRatioCover I J φ hφ g hg hspan f hf).f i ≫
        Spec.map (CommRingCat.ofHom (algebraMap B (chart J f))) ≫
          Spec.map (CommRingCat.ofHom φ) := by
  change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _ ≫ Spec.map _
  simp only [← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  ext a
  exact ratioLift_base I J φ hφ.le f hf (g i) (hg i) a

/-- The ratio-cover construction reaches every input fraction-chart point. -/
theorem actionRatioCover_surjective (z : Spec (.of (chart J f))) :
    ∃ i p, (actionRatioCover I J φ hφ g hg hspan f hf).f i p = z :=
  (actionRatioCover I J φ hφ g hg hspan f hf).openCover.exists_eq z

end FLT.Mazur.BlowupFractionChart
