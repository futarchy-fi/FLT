/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSplitNodalSmoothFormulaComparison
public import FLT.Mazur.WeierstrassSmoothPairAffineDescent
public import FLT.Mazur.WeierstrassSmoothAffinePairDescent

/-!
# Global equality with split-nodal torus multiplication

The four addition charts cover every smooth affine pair. Regular-coordinate
descent extends their comparison to the entire smooth pair, over any base ring.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Limits

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
variable {R : Type u} [CommRing R] (a : Rˣ)

/-- Both nodal laws agree whenever the actual two inputs have affine presentations. -/
theorem splitNodalSmoothAddition_affine {X : Scheme.{u}}
    (t : X ⟶ smoothFactorProduct (splitNodalEquation a))
    (p q : X ⟶ chartScheme (splitNodalEquation a) 2)
    (hp : p ≫ integralCurveChart (splitNodalEquation a) 2 =
      t ≫ pullback.fst _ _ ≫ (integralSmoothOpen (splitNodalEquation a)).ι)
    (hq : q ≫ integralCurveChart (splitNodalEquation a) 2 =
      t ≫ pullback.snd _ _ ≫ (integralSmoothOpen (splitNodalEquation a)).ι) :
    t ≫ smoothFactorAddition (splitNodalEquation a) = t ≫ splitNodalTransportedAddition a := by
  let W := splitNodalEquation a
  obtain ⟨b, hb⟩ := exists_affinePair_of_projections W (t ≫ smoothFactorsInclusion W) p q
    (by simpa only [Category.assoc, smoothFactorsInclusion_fst] using hp)
    (by simpa only [Category.assoc, smoothFactorsInclusion_snd] using hq)
  apply smoothAffinePair_hom_ext W t b hb
  intro i Z u f hf
  have hi : f ≫ additionGlobalDomain W i = (u ≫ t) ≫ smoothFactorsInclusion W := by
    rw [additionGlobalDomain, ← Category.assoc, hf, Category.assoc, hb, Category.assoc]
  simpa only [Category.assoc] using splitNodalSmoothAddition_chart a (u ≫ t) i f hi

/-- On the entire relative smooth nodal curve, the constructed law is torus multiplication. -/
theorem splitNodalSmoothAddition_eq_transported :
    smoothFactorAddition (splitNodalEquation a) = splitNodalTransportedAddition a := by
  apply (cancel_mono (integralSmoothOpen (splitNodalEquation a)).ι).mp
  apply smoothPair_hom_ext_of_affine (splitNodalEquation a)
  intro X t p q hp hq
  simpa only [Category.assoc] using congrArg
    (fun f => f ≫ (integralSmoothOpen (splitNodalEquation a)).ι)
    (splitNodalSmoothAddition_affine a t p q hp hq)

end FLT.Mazur.WeierstrassIntegralChart
