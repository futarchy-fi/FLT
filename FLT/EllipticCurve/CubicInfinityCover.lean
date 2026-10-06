/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.EllipticCurve.CubicFieldCover

/-! # A complete cover of the infinity-chart input product -/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial
set_option backward.isDefEq.respectTransparency false

namespace WeierstrassCurve.CubicCharts
universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

/-- Restrict the infinity input chart product to a finite first or second input. -/
abbrev InfinityFiniteRing (b : Bool) := Localization.Away (infinityPairCoord W b 1)

/-- Restriction to the open where a selected infinity-chart input is finite. -/
def infinityFiniteRestriction (b : Bool) :
    ChartPairRing W true true →ₐ[R] InfinityFiniteRing W b :=
  IsScalarTower.toAlgHom R (ChartPairRing W true true) (InfinityFiniteRing W b)

/-- The three source domains: a finite first input, a finite second input,
or the regular addition domain containing the pair of infinity sections. -/
def InfinityCoverRing : Option Bool → Type u
  | none => InfinityAdditionRing W
  | some b => InfinityFiniteRing W b

instance infinityCoverRingCommRing (i : Option Bool) : CommRing (InfinityCoverRing W i) := by
  cases i <;> dsimp [InfinityCoverRing] <;> infer_instance

instance infinityCoverRingAlgebra (i : Option Bool) : Algebra R (InfinityCoverRing W i) := by
  cases i <;> dsimp [InfinityCoverRing] <;> infer_instance

/-- Restriction from the infinity-chart product to each of the three covering domains. -/
def infinityCoverRestriction : ∀ i, ChartPairRing W true true →ₐ[R] InfinityCoverRing W i
  | none => (infinityAdditionRestriction W).comp (infinitySlopeRestriction W)
  | some b => infinityFiniteRestriction W b

theorem infinityCoverRestriction_isOpenImmersion (i : Option Bool) :
    IsOpenImmersion (Spec.map (CommRingCat.ofHom (infinityCoverRestriction W i).toRingHom)) := by
  cases i with
  | none =>
    have : IsOpenImmersion (Spec.map
        (CommRingCat.ofHom (algebraMap (InfinitySlopeRing W) (InfinityAdditionRing W)))) :=
      IsOpenImmersion.of_isLocalization (infinitySumProjective W 1)
    have : IsOpenImmersion (Spec.map (CommRingCat.ofHom
        (algebraMap (ChartPairRing W true true) (InfinitySlopeRing W)))) :=
      IsOpenImmersion.of_isLocalization (infinitySlopeDenominator W)
    change IsOpenImmersion (Spec.map
      (CommRingCat.ofHom (algebraMap (ChartPairRing W true true) (InfinitySlopeRing W)) ≫
        CommRingCat.ofHom (algebraMap (InfinitySlopeRing W) (InfinityAdditionRing W))))
    rw [Spec.map_comp]
    infer_instance
  | some b =>
    change IsOpenImmersion (Spec.map (CommRingCat.ofHom
      (algebraMap (ChartPairRing W true true) (InfinityFiniteRing W b))))
    exact IsOpenImmersion.of_isLocalization (infinityPairCoord W b 1)

theorem infinitySlope_sum_of_inputs_zero {S : Type u} [CommRing S] [Algebra R S]
    (f : InfinitySlopeRing W →ₐ[R] S)
    (h : ∀ b i, f (infinitySlopeCoord W b i) = 0) :
    f ∘ infinitySumProjective W = ![0, 1, 0] := by
  have hn := infinityChordNumerator_baseChange W f
    (infinitySlopeCoord W false 0) (infinitySlopeCoord W true 0) (infinitySlopeCoord W false 1)
  simp only [h] at hn
  have hz : f (infinitySlope W) = 0 := by
    have hh : f (infinityChordNumerator (W.map (algebraMap R (InfinitySlopeRing W)))
        (infinitySlopeCoord W false 0) (infinitySlopeCoord W true 0)
        (infinitySlopeCoord W false 1)) = 0 :=
      hn.trans (by simp [infinityChordNumerator])
    unfold infinitySlope
    rw [map_mul, hh, zero_mul]
  have hc := infinityChord_baseChange W f
    (infinitySlopeCoord W false 0) (infinitySlopeCoord W false 1)
    (infinitySlopeCoord W true 0) (infinitySlope W)
  simp only [h, hz, infinityChord_origin] at hc
  exact hc

theorem infinityCover_field_lift {K : Type u} [Field K] [Algebra R K]
    (f : ChartPairRing W true true →ₐ[R] K) :
    ∃ i, ∃ g : InfinityCoverRing W i →ₐ[R] K, g.comp (infinityCoverRestriction W i) = f := by
  by_cases hv : ∃ b, f (infinityPairCoord W b 1) ≠ 0
  · obtain ⟨b, hb⟩ := hv
    let g : InfinityFiniteRing W b →ₐ[R] K :=
      IsLocalization.Away.liftAlgHom (infinityPairCoord W b 1) (f := f) hb.isUnit
    refine ⟨some b, g, ?_⟩
    apply AlgHom.ext
    intro x
    change g (algebraMap (ChartPairRing W true true) (InfinityFiniteRing W b) x) = f x
    simp [g, IsLocalization.Away.liftAlgHom_apply]
  · push Not at hv
    have hc (b : Bool) (i : Fin 2) : f (infinityPairCoord W b i) = 0 := by
      have hp := chartPointCoords_equation W true (f.comp (infinityPairInput W b))
      fin_cases i
      · exact Projective.X_eq_zero_of_Z_eq_zero hp (hv b)
      · exact hv b
    have hd : f (infinitySlopeDenominator W) = 1 := by
      have hh := infinityChordDenominator_baseChange W f
        (infinityPairCoord W true 0) (infinityPairCoord W false 1) (infinityPairCoord W true 1)
      simp only [hc] at hh
      exact hh.trans (by simp [infinityChordDenominator])
    let a : InfinitySlopeRing W →ₐ[R] K :=
      IsLocalization.Away.liftAlgHom (infinitySlopeDenominator W) (f := f)
        (by rw [hd]; exact isUnit_one)
    have ha (x : ChartPairRing W true true) : a (infinitySlopeRestriction W x) = f x := by
      simp [a, infinitySlopeRestriction, IsLocalization.Away.liftAlgHom_apply]
    have hzero (b : Bool) (i : Fin 2) : a (infinitySlopeCoord W b i) = 0 :=
      (ha (infinityPairCoord W b i)).trans (hc b i)
    have hy : a (infinitySumProjective W 1) = 1 :=
      congrFun (infinitySlope_sum_of_inputs_zero W a hzero) 1
    let g : InfinityAdditionRing W →ₐ[R] K :=
      IsLocalization.Away.liftAlgHom (infinitySumProjective W 1) (f := a)
        (by rw [hy]; exact isUnit_one)
    refine ⟨none, g, ?_⟩
    apply AlgHom.ext
    intro x
    change g (infinityAdditionRestriction W (infinitySlopeRestriction W x)) = f x
    have hg (z : InfinitySlopeRing W) : g (infinityAdditionRestriction W z) = a z := by
      simp [g, infinityAdditionRestriction, IsLocalization.Away.liftAlgHom_apply]
    exact (hg _).trans (ha x)

/-- The two finite-input opens and the infinity-pair addition domain cover the
entire product of infinity charts, as an actual scheme open cover. -/
def infinityChartAdditionCover : (Spec (.of (ChartPairRing W true true))).OpenCover :=
  affineCoverOfFieldLifts (R := R) (InfinityCoverRing W) (infinityCoverRestriction W)
    (infinityCoverRestriction_isOpenImmersion W) (fun _ _ _ f ↦ infinityCover_field_lift W f)

end WeierstrassCurve.CubicCharts
