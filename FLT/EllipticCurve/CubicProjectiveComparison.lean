/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.EllipticCurve.CubicInfinityIdentity
public import FLT.EllipticCurve.CubicChartPoint

/-! # Scheme equality from homogeneous coordinate comparisons -/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial
set_option backward.isDefEq.respectTransparency false

namespace WeierstrassCurve.CubicCharts
universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

private theorem chart_algHom_ext {S : Type u} [CommRing S] [Algebra R S] (b : Bool)
    (f g : Ring W b →ₐ[R] S)
    (h : ∀ i, f (coord W b i) = g (coord W b i)) : f = g := by
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  exact h

/-- Equality of all homogeneous cross products identifies maps into the glued cubic.
This criterion works for any combination of output charts over arbitrary rings. -/
theorem chart_point_agreement_of_cross {S : Type u} [CommRing S] [Algebra R S]
    (b c : Bool) (f : Ring W b →ₐ[R] S) (g : Ring W c →ₐ[R] S)
    (h : ∀ i j, chartPointCoords W b f i * chartPointCoords W c g j =
      chartPointCoords W c g i * chartPointCoords W b f j) :
    Spec.map (CommRingCat.ofHom f.toRingHom) ≫ sourceChart W b =
      Spec.map (CommRingCat.ofHom g.toRingHom) ≫ sourceChart W c := by
  cases b <;> cases c
  · have he : f = g := by
      apply chart_algHom_ext
      intro i
      have hh := h (if i = 0 then 0 else 1) 2
      fin_cases i <;> simpa [chartPointCoords] using hh
    rw [he]
  · apply chart_point_agreement
    · simpa [chartPointCoords] using h 1 2
    · simpa [chartPointCoords] using h 0 2
  · symm
    apply chart_point_agreement
    · simpa [chartPointCoords, mul_comm] using h 2 1
    · simpa [chartPointCoords, mul_comm] using h 2 0
  · have he : f = g := by
      apply chart_algHom_ext
      intro i
      have hh := h (if i = 0 then 0 else 2) 1
      fin_cases i <;> simpa [chartPointCoords] using hh
    rw [he]

/-- Cross-product comparison survives either normalization of the homogeneous coordinates. -/
theorem chart_point_agreement_of_scaled {S : Type u} [CommRing S] [Algebra R S]
    (b c : Bool) (f : Ring W b →ₐ[R] S) (g : Ring W c →ₐ[R] S)
    (P Q : Fin 3 → S) (s t : S)
    (hf : ∀ i, chartPointCoords W b f i = P i * s)
    (hg : ∀ i, chartPointCoords W c g i = Q i * t)
    (h : ∀ i j, P i * Q j = Q i * P j) :
    Spec.map (CommRingCat.ofHom f.toRingHom) ≫ sourceChart W b =
      Spec.map (CommRingCat.ofHom g.toRingHom) ≫ sourceChart W c := by
  apply chart_point_agreement_of_cross
  intro i j
  rw [hf, hf, hg, hg]
  linear_combination s * t * h i j

theorem chartPointCoords_baseChange {A B : Type*} [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] (b : Bool) (f : A →ₐ[R] B) (g : Ring W b →ₐ[R] A) :
    chartPointCoords W b (f.comp g) = f ∘ chartPointCoords W b g := by
  ext i
  cases b <;> fin_cases i <;> simp [chartPointCoords]

theorem projectiveAdditionSum_normalized (b c d : Bool) (i : Fin 3) :
    chartPointCoords W d (projectiveAdditionSum W b c d) i =
      projectiveAdditionRestriction W b c d (chartPairSum W b c i) *
        projectiveAdditionInv W b c d := by
  cases d <;> fin_cases i
  · exact projectiveAdditionSum_coord W b c false 0
  · exact projectiveAdditionSum_coord W b c false 1
  · exact (IsLocalization.Away.mul_invSelf
      (S := ProjectiveAdditionRing W b c false)
      (projectiveAdditionDenominator W b c false)).symm
  · exact projectiveAdditionSum_coord W b c true 0
  · exact (IsLocalization.Away.mul_invSelf
      (S := ProjectiveAdditionRing W b c true)
      (projectiveAdditionDenominator W b c true)).symm
  · exact projectiveAdditionSum_coord W b c true 1

theorem projectiveAdditionSum_normalized_map {S : Type u} [CommRing S] [Algebra R S]
    (b c d : Bool) (f : ProjectiveAdditionRing W b c d →ₐ[R] S) (i : Fin 3) :
    chartPointCoords W d (f.comp (projectiveAdditionSum W b c d)) i =
      f (projectiveAdditionRestriction W b c d (chartPairSum W b c i)) *
        f (projectiveAdditionInv W b c d) := by
  rw [chartPointCoords_baseChange]
  change f (chartPointCoords W d (projectiveAdditionSum W b c d) i) = _
  rw [projectiveAdditionSum_normalized, map_mul]

/-- The two target normalizations of the same projective law define the same
scheme morphism on every common domain. -/
theorem projectiveAddition_target_agreement {S : Type u} [CommRing S] [Algebra R S]
    (b c d e : Bool)
    (f : ProjectiveAdditionRing W b c d →ₐ[R] S)
    (g : ProjectiveAdditionRing W b c e →ₐ[R] S)
    (h : f.comp (projectiveAdditionRestriction W b c d) =
      g.comp (projectiveAdditionRestriction W b c e)) :
    Spec.map (CommRingCat.ofHom (f.comp (projectiveAdditionSum W b c d)).toRingHom) ≫
        sourceChart W d =
      Spec.map (CommRingCat.ofHom (g.comp (projectiveAdditionSum W b c e)).toRingHom) ≫
        sourceChart W e := by
  apply chart_point_agreement_of_scaled W d e _ _
    (fun i ↦ f (projectiveAdditionRestriction W b c d (chartPairSum W b c i)))
    (fun i ↦ g (projectiveAdditionRestriction W b c e (chartPairSum W b c i)))
    (f (projectiveAdditionInv W b c d)) (g (projectiveAdditionInv W b c e))
    (projectiveAdditionSum_normalized_map W b c d f)
    (projectiveAdditionSum_normalized_map W b c e g)
  intro i j
  have hi := DFunLike.congr_fun h (chartPairSum W b c i)
  have hj := DFunLike.congr_fun h (chartPairSum W b c j)
  change f (projectiveAdditionRestriction W b c d (chartPairSum W b c i)) =
    g (projectiveAdditionRestriction W b c e (chartPairSum W b c i)) at hi
  change f (projectiveAdditionRestriction W b c d (chartPairSum W b c j)) =
    g (projectiveAdditionRestriction W b c e (chartPairSum W b c j)) at hj
  rw [hi, hj]

end WeierstrassCurve.CubicCharts
