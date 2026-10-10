/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSmoothCrossAffine
public import FLT.Mazur.WeierstrassPolynomialInputCurveComparison

/-!
# Comparing smooth addition across polynomial input presentations

The original polynomial output-Z domain is invariant under changes of input
normalization. Its smooth restriction compares all four chart laws.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

/-- A polynomial domain with smooth original inputs lifts to its actual smooth restriction. -/
def smoothPolynomialLift (b c : Bool) (t : Fin 3) {X : Scheme.{u}}
    (g : X ⟶ Spec (.of (AdditionOutputOpen W
      (productChartCoordinate b) (productChartCoordinate c) t)))
    (f : X ⟶ (smoothProductChartOpen W b c).toScheme)
    (h : g ≫ projectiveAdditionInclusion W
      (productChartCoordinate b) (productChartCoordinate c) t =
        f ≫ (smoothProductChartOpen W b c).ι) :
    X ⟶ (polynomialSmoothInputOpen W
      (productChartCoordinate b) (productChartCoordinate c) t).toScheme :=
  IsOpenImmersion.lift (polynomialSmoothInputOpen W
    (productChartCoordinate b) (productChartCoordinate c) t).ι g (by
      rw [Scheme.Opens.range_ι]
      rintro _ ⟨p, rfl⟩
      apply (polynomialSmoothInputOpen_preimage W b c t).le
      change (g ≫ projectiveAdditionInclusion W
        (productChartCoordinate b) (productChartCoordinate c) t) p ∈
          smoothProductChartOpen W b c
      rw [h]
      exact (f p).property)

/-- The lifted polynomial point has exactly the prescribed smooth input pair. -/
@[reassoc] theorem smoothPolynomialLift_inputs (b c : Bool) (t : Fin 3) {X : Scheme.{u}}
    (g : X ⟶ Spec (.of (AdditionOutputOpen W
      (productChartCoordinate b) (productChartCoordinate c) t)))
    (f : X ⟶ (smoothProductChartOpen W b c).toScheme)
    (h : g ≫ projectiveAdditionInclusion W
      (productChartCoordinate b) (productChartCoordinate c) t =
        f ≫ (smoothProductChartOpen W b c).ι) :
    smoothPolynomialLift W b c t g f h ≫ smoothPolynomialToInputs W b c t = f := by
  apply (cancel_mono (smoothProductChartOpen W b c).ι).mp
  rw [Category.assoc, smoothPolynomialToInputs_inclusion,
    smoothPolynomialInput, ← Category.assoc]
  exact (congrArg (fun a => a ≫ projectiveAdditionInclusion W
    (productChartCoordinate b) (productChartCoordinate c) t)
    (IsOpenImmersion.lift_fac _ _ _)).trans h

/-- Smooth chart addition agrees with any polynomial output-Z presentation of the same inputs. -/
theorem smoothInputAddition_commonPolynomial (b c d e : Bool) {X : Scheme.{u}}
    (f : X ⟶ (smoothProductChartOpen W b c).toScheme)
    (g : X ⟶ Spec (.of (AdditionOutputOpen W
      (productChartCoordinate d) (productChartCoordinate e) 2)))
    (h : f ≫ smoothProductChartInput W b c =
      g ≫ projectiveAdditionInclusion W (productChartCoordinate d) (productChartCoordinate e) 2 ≫
        integralCurveProductChart W d e) :
    f ≫ smoothInputAddition W b c ≫ (integralSmoothOpen W).ι =
      g ≫ Spec.map (CommRingCat.ofHom (projectiveAdditionChart W
        (productChartCoordinate d) (productChartCoordinate e) 2).toRingHom) ≫
          integralCurveChart W 2 := by
  let j := productChartCoordinate d
  let k := productChartCoordinate e
  let j' := productChartCoordinate b
  let k' := productChartCoordinate c
  obtain ⟨v, hv, hv'⟩ := integralProductOverlap_exists_lift W d e b c
    (g ≫ projectiveAdditionInclusion W j k 2) (f ≫ (smoothProductChartOpen W b c).ι)
    (by simpa only [smoothProductChartInput, Category.assoc] using h.symm)
  let l := (inputPolynomial_isPullback W j k j' k' 2).lift v g hv
  let q := l ≫ Spec.map (CommRingCat.ofHom (inputPolynomialOther W j k j' k' 2).toRingHom)
  have hq : q ≫ projectiveAdditionInclusion W j' k' 2 =
      f ≫ (smoothProductChartOpen W b c).ι := by
    rw [Category.assoc, inputPolynomialOther_inclusion, ← Category.assoc,
      IsPullback.lift_fst]
    exact hv'
  let s := smoothPolynomialLift W b c 2 q f hq
  have hs : s ≫ smoothPolynomialToInputs W b c 2 = f :=
    smoothPolynomialLift_inputs W b c 2 q f hq
  rw [← hs, Category.assoc, smoothInputAddition_polynomial_assoc,
    polynomialSmoothChart_inclusion, ← Category.assoc]
  have hsi : s ≫ (polynomialSmoothInputOpen W j' k' 2).ι = q :=
    IsOpenImmersion.lift_fac _ _ _
  rw [hsi]
  have he := congrArg (fun a => l ≫ a ≫ integralCurveChart W 2)
    (inputPolynomialAddition_spec W j k j' k' 2)
  simpa only [q, Category.assoc, l, IsPullback.lift_snd_assoc] using he

end FLT.Mazur.WeierstrassIntegralChart
