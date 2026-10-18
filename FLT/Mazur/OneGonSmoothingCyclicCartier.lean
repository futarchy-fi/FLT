/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OneGonCompleteUniversalCyclicFamily
public import FLT.Mazur.WeierstrassSmoothOpenRelativeDimension
public import FLT.Mazur.RelativeSums

/-!
# The full cyclic subgroup is a relative Cartier divisor on the smoothing

The entire relative smooth group has dimension one. Its universally faithful
cyclic sections therefore give the actual relative Cartier generator orbit
on the whole proper curve, including across the singular one-gon fiber.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory MonObj
namespace FLT.Mazur.OneGonSmoothing
open FCurve WeierstrassIntegralChart
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] (t : R) (n : ℕ) [NeZero n]
  {T : Scheme} (g : T ⟶ Spec (.of R))
  (f : Over.mk g ⟶ relativeCyclicParameter t n)

/-- The original smoothing's whole smooth group has relative dimension one. -/
theorem relativeGroup_dimension : SmoothOfRelativeDimension 1 (relativeGroup t).X.hom :=
  integralSmoothStructure_relativeDimension (equation t)

/-- Every actual base-changed smooth group retains relative dimension one. -/
theorem relativeTestGroup_dimension :
    SmoothOfRelativeDimension 1 (relativeTestGroup t g).X.hom := by
  let _ := relativeGroup_dimension t
  exact MorphismProperty.pullback_snd (P := @SmoothOfRelativeDimension 1)
    (relativeGroup t).X.hom g inferInstance

/-- The full closed subgroup ideal is relative Cartier on the original entire smoothing test. -/
theorem relativeCyclicIdeal_cartier :
    RelativeEffectiveCartier ((Over.pullback g).obj (family t)).hom
      (relativeCyclicIdeal t n g f) := by
  let _ := relativeTestFamily_proper t g
  have : SmoothOfRelativeDimension 1 ((relativeTestInclusion t g).left ≫
      ((Over.pullback g).obj (family t)).hom) := by
    rw [(relativeTestInclusion t g).w]
    exact relativeTestGroup_dimension t g
  rw [relativeCyclicIdeal_product]
  exact relativeEffectiveCartier_smoothOpen_section_prod (relativeTestInclusion t g).left
    ((Over.pullback g).obj (family t)).hom Finset.univ
    (fun i : ZMod n ↦ (relativeCyclicMarking t n g f (.ofAdd i)).left)
    (fun i _ ↦ (relativeCyclicMarking t n g f (.ofAdd i) ≫ relativeTestInclusion t g).w)

/-- The original full generator orbit remains relative Cartier after every further base change. -/
theorem relativeCyclicIdeal_cartier_baseChange {U : Scheme} (k : U ⟶ T) :
    RelativeEffectiveCartier (pullback.snd ((Over.pullback g).obj (family t)).hom k)
      ((relativeCyclicIdeal t n g f).comap
        (pullback.fst ((Over.pullback g).obj (family t)).hom k)) :=
  relativeCartierBaseChange _ k _ (relativeCyclicIdeal_cartier t n g f)

/-- The actual universal subgroup is Cartier across the complete family's singular fibers. -/
theorem completeUniversalCyclicMap_cartier (K : Type) [Field K] :
    RelativeEffectiveCartier (completeUniversalCyclicFamily K n).hom
      (completeUniversalCyclicMap K n).left.ker :=
  relativeCyclicIdeal_cartier (PowerSeries.X : PowerSeries K) n
    (relativeCyclicParameter (PowerSeries.X : PowerSeries K) n).hom (𝟙 _)

end FLT.Mazur.OneGonSmoothing
