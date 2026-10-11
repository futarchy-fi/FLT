/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassLeftSmoothInputAddition
public import FLT.Mazur.WeierstrassPolynomialInputCurveComparison

/-!
# Enlarged addition across affine and polynomial input presentations

Actual global input equalities give simultaneous coordinate overlaps. The
original affine and polynomial comparisons apply with only the first input smooth.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

/-- Every chart law agrees with the enlarged affine law on common global inputs. -/
theorem leftSmoothInputAddition_commonAffine (b c : Bool) {X : Scheme.{u}}
    (f : X ⟶ (leftSmoothProductChartOpen W b c).toScheme)
    (a : X ⟶ (leftSmoothAffineInputOpen W).toScheme)
    (h : f ≫ leftSmoothProductChartInput W b c =
      a ≫ (leftSmoothAffineInputOpen W).ι ≫ integralCurveProductChart W false false) :
    f ≫ leftSmoothInputAddition W b c = a ≫ leftSmoothAffineAddition W := by
  obtain ⟨v, hv, ha⟩ := integralProductOverlap_exists_lift W b c false false
    (f ≫ (leftSmoothProductChartOpen W b c).ι) (a ≫ (leftSmoothAffineInputOpen W).ι)
    (by simpa only [leftSmoothProductChartInput, Category.assoc] using h)
  let l : X ⟶ (leftSmoothAffineOverlapOpen W b c).toScheme :=
    IsOpenImmersion.lift (leftSmoothAffineOverlapOpen W b c).ι v (by
      rw [Scheme.Opens.range_ι, leftSmoothAffineOverlapOpen_eq]
      rintro _ ⟨p, rfl⟩
      change (v ≫ integralProductOverlapFst W b c false false) p ∈
        leftSmoothProductChartOpen W b c
      rw [hv]
      exact (f p).property)
  have hl : l ≫ (leftSmoothAffineOverlapOpen W b c).ι = v :=
    IsOpenImmersion.lift_fac _ _ _
  have hi : f ≫ (leftSmoothProductChartOpen W b c).ι =
      l ≫ leftSmoothAffineOverlapInput W b c := by
    rw [leftSmoothAffineOverlapInput, ← Category.assoc, hl, hv]
  have hla : l ≫ leftSmoothAffineOverlapToInputs W b c = a := by
    apply (cancel_mono (leftSmoothAffineInputOpen W).ι).mp
    rw [Category.assoc, leftSmoothAffineOverlapToInputs_inclusion, ← Category.assoc, hl]
    exact ha
  rw [leftSmoothInputAddition_affine W b c f l hi,
    leftSmoothAffineOverlapAddition, ← Category.assoc, hla]

/-- Every chart law agrees with any polynomial output-Z presentation of the same inputs. -/
theorem leftSmoothInputAddition_commonPolynomial (b c d e : Bool) {X : Scheme.{u}}
    (f : X ⟶ (leftSmoothProductChartOpen W b c).toScheme)
    (g : X ⟶ Spec (.of (AdditionOutputOpen W
      (productChartCoordinate d) (productChartCoordinate e) 2)))
    (h : f ≫ leftSmoothProductChartInput W b c =
      g ≫ projectiveAdditionInclusion W (productChartCoordinate d) (productChartCoordinate e) 2 ≫
        integralCurveProductChart W d e) :
    f ≫ leftSmoothInputAddition W b c =
      g ≫ Spec.map (CommRingCat.ofHom (projectiveAdditionChart W
        (productChartCoordinate d) (productChartCoordinate e) 2).toRingHom) ≫
          integralCurveChart W 2 := by
  let j := productChartCoordinate d
  let k := productChartCoordinate e
  let j' := productChartCoordinate b
  let k' := productChartCoordinate c
  obtain ⟨v, hv, hv'⟩ := integralProductOverlap_exists_lift W d e b c
    (g ≫ projectiveAdditionInclusion W j k 2) (f ≫ (leftSmoothProductChartOpen W b c).ι)
    (by simpa only [leftSmoothProductChartInput, Category.assoc] using h.symm)
  let l := (inputPolynomial_isPullback W j k j' k' 2).lift v g hv
  let q := l ≫ Spec.map (CommRingCat.ofHom (inputPolynomialOther W j k j' k' 2).toRingHom)
  have hq : q ≫ projectiveAdditionInclusion W j' k' 2 =
      f ≫ (leftSmoothProductChartOpen W b c).ι := by
    rw [Category.assoc, inputPolynomialOther_inclusion, ← Category.assoc,
      IsPullback.lift_fst]
    exact hv'
  rw [leftSmoothInputAddition_polynomial W b c f q hq.symm]
  have he := congrArg (fun a => l ≫ a ≫ integralCurveChart W 2)
    (inputPolynomialAddition_spec W j k j' k' 2)
  simpa only [q, Category.assoc, l, IsPullback.lift_snd_assoc] using he

end FLT.Mazur.WeierstrassIntegralChart
