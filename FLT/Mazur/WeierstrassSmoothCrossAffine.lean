/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSmoothInputAddition

/-!
# Comparing smooth addition across affine input presentations

Equality of the global input pairs produces a simultaneous chart overlap.
Its smooth restriction identifies every chart law with smooth affine addition.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

/-- The original global product inclusion of a smooth input chart. -/
def smoothProductChartInput (b c : Bool) :
    (smoothProductChartOpen W b c).toScheme ⟶ integralCurveProduct W :=
  (smoothProductChartOpen W b c).ι ≫ integralCurveProductChart W b c

/-- Each smooth chart is still open in the original product. -/
instance smoothProductChartInput_isOpenImmersion (b c : Bool) :
    IsOpenImmersion (smoothProductChartInput W b c) :=
  inferInstanceAs (IsOpenImmersion (_ ≫ _))

/-- Every smooth chart agrees with the smooth affine law on common global inputs. -/
theorem smoothInputAddition_commonAffine (b c : Bool) {X : Scheme.{u}}
    (f : X ⟶ (smoothProductChartOpen W b c).toScheme)
    (a : X ⟶ (smoothAffineInputOpen W).toScheme)
    (h : f ≫ smoothProductChartInput W b c =
      a ≫ (smoothAffineInputOpen W).ι ≫ integralCurveProductChart W false false) :
    f ≫ smoothInputAddition W b c = a ≫ smoothAffineAddition W := by
  obtain ⟨v, hv, ha⟩ := integralProductOverlap_exists_lift W b c false false
    (f ≫ (smoothProductChartOpen W b c).ι) (a ≫ (smoothAffineInputOpen W).ι)
    (by simpa only [smoothProductChartInput, Category.assoc] using h)
  have hs : Set.range (v ≫ integralProductOverlapFst W b c false false) ⊆
      smoothProductChartOpen W b c := by
    rw [hv]
    rintro _ ⟨p, rfl⟩
    exact (f p).property
  let l := smoothAffineOverlapLift W b c v hs
  have hl : l ≫ smoothAffineOverlapToChart W b c = f := by
    apply (cancel_mono (smoothProductChartOpen W b c).ι).mp
    rw [Category.assoc, smoothAffineOverlapToChart_inclusion]
    exact (smoothAffineOverlapLift_input W b c v hs).trans hv
  have hla : l ≫ smoothAffineOverlapToInputs W b c = a := by
    apply (cancel_mono (smoothAffineInputOpen W).ι).mp
    rw [Category.assoc, smoothAffineOverlapToInputs_inclusion, ← Category.assoc]
    have hi : l ≫ (smoothAffineOverlapOpen W b c).ι = v :=
      IsOpenImmersion.lift_fac _ _ _
    rw [hi]
    exact ha
  rw [← hl, Category.assoc, smoothInputAddition_affine,
    smoothAffineOverlapAddition, ← Category.assoc, hla]

/-- The affine normalization retains the global input pair after smooth restriction. -/
@[reassoc] theorem smoothAffineOverlapToInputs_global (b c : Bool) :
    smoothAffineOverlapToInputs W b c ≫ (smoothAffineInputOpen W).ι ≫
        integralCurveProductChart W false false =
      smoothAffineOverlapToChart W b c ≫ smoothProductChartInput W b c := by
  rw [smoothProductChartInput, smoothAffineOverlapToChart_inclusion_assoc,
    smoothAffineOverlapToInputs_inclusion_assoc, smoothAffineOverlapInput, Category.assoc]
  exact congrArg (fun f => (smoothAffineOverlapOpen W b c).ι ≫ f)
    (integralProductOverlap_condition W b c false false).symm

end FLT.Mazur.WeierstrassIntegralChart
