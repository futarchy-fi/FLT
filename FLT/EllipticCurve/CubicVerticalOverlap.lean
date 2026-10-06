/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.EllipticCurve.CubicVerticalAddition

/-! # Agreement of the two vertical chord constructions -/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial
open scoped TensorProduct
set_option backward.isDefEq.respectTransparency false

namespace WeierstrassCurve.CubicCharts
universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

/-- Proportional chord parameters give proportional X and Y output coordinates. -/
theorem chord_cross_xy (x₁ x₂ y₁ s t u v : R) (h : s * v = u * t) :
    chordX W x₁ x₂ s t * chordY W x₁ x₂ y₁ u v =
      chordX W x₁ x₂ u v * chordY W x₁ x₂ y₁ s t := by
  unfold chordX chordY chordXNumerator
  linear_combination
    (s ^ 2 * u ^ 2 + W.a₁ * s * u * (s * v + u * t) -
      (W.a₂ + x₁ + x₂) * ((s * v) ^ 2 + s * v * u * t + (u * t) ^ 2) +
      (W.a₂ + 2 * x₁ + x₂ + W.a₁ ^ 2) * s * t * u * v +
      (-W.a₁ * (W.a₂ + x₁ + x₂) - y₁ - W.a₃) * t * v * (s * v + u * t) +
      (W.a₁ * (W.a₁ * (W.a₂ + x₁ + x₂) - y₁ - W.a₃) +
        (W.a₂ + x₁ + x₂) * (W.a₂ + 2 * x₁ + x₂ - W.a₁ ^ 2)) * t ^ 2 * v ^ 2) * h

/-- Proportional chord parameters give proportional Z and Y output coordinates. -/
theorem chord_cross_zy (x₁ x₂ y₁ s t u v : R) (h : s * v = u * t) :
    t ^ 3 * chordY W x₁ x₂ y₁ u v = v ^ 3 * chordY W x₁ x₂ y₁ s t := by
  unfold chordY chordXNumerator
  linear_combination
    ((s * v) ^ 2 + s * v * u * t + (u * t) ^ 2 +
      2 * W.a₁ * t * v * (s * v + u * t) -
      (W.a₂ + 2 * x₁ + x₂ - W.a₁ ^ 2) * t ^ 2 * v ^ 2) * h

/-- Cross multiplication identifies normalized coordinates when both denominators are units. -/
theorem normalized_eq_of_cross {a b c d i j : R} (hb : b * i = 1)
    (hd : d * j = 1) (h : a * d = c * b) : a * i = c * j := by
  linear_combination i * j * h - a * i * hd + c * j * hb

theorem pairChord_relation :
    pairChordS W false * pairChordT W true = pairChordS W true * pairChordT W false := by
  have h := chord_relation (W.map (algebraMap R (AffinePairRing W)))
    (pair_input_equation W false) (pair_input_equation W true)
  exact h.trans (mul_comm (pairChordT W false) (pairChordS W true))

theorem pairChord_cross_xy :
    pairChordX W false * pairChordY W true = pairChordX W true * pairChordY W false :=
  chord_cross_xy (W.map (algebraMap R (AffinePairRing W)))
    (pairCoord W false 0) (pairCoord W true 0) (pairCoord W false 1)
    (pairChordS W false) (pairChordT W false) (pairChordS W true) (pairChordT W true)
    (pairChord_relation W)

theorem pairChord_cross_zy :
    pairChordT W false ^ 3 * pairChordY W true =
      pairChordT W true ^ 3 * pairChordY W false :=
  chord_cross_zy (W.map (algebraMap R (AffinePairRing W)))
    (pairCoord W false 0) (pairCoord W true 0) (pairCoord W false 1)
    (pairChordS W false) (pairChordT W false) (pairChordS W true) (pairChordT W true)
    (pairChord_relation W)

/-- Compatibility after any common restriction of the two vertical domains. -/
theorem verticalSum_compatible {S : Type*} [CommRing S] [Algebra R S]
    (f : VerticalRing W false →ₐ[R] S) (g : VerticalRing W true →ₐ[R] S)
    (h : f.comp (verticalRestriction W false) = g.comp (verticalRestriction W true)) :
    f.comp (verticalSum W false) = g.comp (verticalSum W true) := by
  have hv (x : AffinePairRing W) :
      f (verticalRestriction W false x) = g (verticalRestriction W true x) :=
    DFunLike.congr_fun h x
  have ha := congrArg f
    (IsLocalization.Away.mul_invSelf (S := VerticalRing W false) (pairChordY W false))
  have hb := congrArg g
    (IsLocalization.Away.mul_invSelf (S := VerticalRing W true) (pairChordY W true))
  simp only [map_mul, map_one] at ha hb
  change f (verticalRestriction W false (pairChordY W false)) * f (verticalInv W false) = 1 at ha
  change g (verticalRestriction W true (pairChordY W true)) * g (verticalInv W true) = 1 at hb
  rw [← hv] at hb
  have hx := congrArg (f.comp (verticalRestriction W false)) (pairChord_cross_xy W)
  have hz := congrArg (f.comp (verticalRestriction W false)) (pairChord_cross_zy W)
  simp only [map_mul, AlgHom.comp_apply] at hx hz
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  intro i
  change f (verticalSum W false (coord W true i)) = g (verticalSum W true (coord W true i))
  rw [verticalSum_coord, verticalSum_coord]
  fin_cases i
  · change f (verticalRestriction W false (pairChordX W false) * verticalInv W false) =
      g (verticalRestriction W true (pairChordX W true) * verticalInv W true)
    rw [map_mul, map_mul, ← hv]
    exact normalized_eq_of_cross ha hb hx
  · change f (verticalRestriction W false (pairChordT W false ^ 3) * verticalInv W false) =
      g (verticalRestriction W true (pairChordT W true ^ 3) * verticalInv W true)
    rw [map_mul, map_mul, ← hv]
    exact normalized_eq_of_cross ha hb hz

/-- The intersection ring of the two vertical opens. -/
abbrev VerticalOverlapRing :=
  VerticalRing W false ⊗[AffinePairRing W] VerticalRing W true

/-- Restriction from the first vertical domain. -/
def verticalLeft : VerticalRing W false →ₐ[R] VerticalOverlapRing W :=
  (Algebra.TensorProduct.includeLeft :
    VerticalRing W false →ₐ[AffinePairRing W] VerticalOverlapRing W).restrictScalars R

/-- Restriction from the second vertical domain. -/
def verticalRight : VerticalRing W true →ₐ[R] VerticalOverlapRing W :=
  (Algebra.TensorProduct.includeRight :
    VerticalRing W true →ₐ[AffinePairRing W] VerticalOverlapRing W).restrictScalars R

theorem vertical_restrictions_agree :
    (verticalLeft W).comp (verticalRestriction W false) =
      (verticalRight W).comp (verticalRestriction W true) := by
  apply AlgHom.ext
  intro x
  have hl := (Algebra.TensorProduct.includeLeft :
    VerticalRing W false →ₐ[AffinePairRing W] VerticalOverlapRing W).commutes x
  have hr := (Algebra.TensorProduct.includeRight :
    VerticalRing W true →ₐ[AffinePairRing W] VerticalOverlapRing W).commutes x
  exact hl.trans hr.symm

theorem vertical_sum_agreement :
    (verticalLeft W).comp (verticalSum W false) =
      (verticalRight W).comp (verticalSum W true) :=
  verticalSum_compatible W (verticalLeft W) (verticalRight W) (vertical_restrictions_agree W)

/-- The two additions to the infinity chart agree on their common open. -/
theorem vertical_addition_agreement :
    Spec.map (CommRingCat.ofHom (verticalLeft W).toRingHom) ≫ verticalAddition W false =
      Spec.map (CommRingCat.ofHom (verticalRight W).toRingHom) ≫ verticalAddition W true := by
  unfold verticalAddition
  rw [← Category.assoc, ← Spec.map_comp, ← Category.assoc, ← Spec.map_comp]
  congr 1
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro x
  exact DFunLike.congr_fun (vertical_sum_agreement W) x

/-- This common domain is the actual scheme-theoretic intersection. -/
theorem vertical_overlap_isPullback :
    IsPullback
      (Spec.map (CommRingCat.ofHom (verticalLeft W).toRingHom))
      (Spec.map (CommRingCat.ofHom (verticalRight W).toRingHom))
      (Spec.map (CommRingCat.ofHom (algebraMap (AffinePairRing W) (VerticalRing W false))))
      (Spec.map (CommRingCat.ofHom (algebraMap (AffinePairRing W) (VerticalRing W true)))) := by
  exact isPullback_SpecMap_of_isPushout _ _ _ _
    (CommRingCat.isPushout_tensorProduct (AffinePairRing W)
      (VerticalRing W false) (VerticalRing W true))

end WeierstrassCurve.CubicCharts
