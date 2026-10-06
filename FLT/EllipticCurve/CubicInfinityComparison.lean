/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.EllipticCurve.CubicProjectiveComparison

/-! # Comparing the infinity chord with the projective secant law -/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial
set_option backward.isDefEq.respectTransparency false

namespace WeierstrassCurve.CubicCharts
universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

/-- The infinity-chart chord removes the cubic factor that makes the projective
secant formula vanish on the diagonal. The equality holds before any cancellation. -/
theorem projective_addXYZ_infinityChord {u v r w l : R}
    (hP : W.toProjective.Equation ![u, 1, v])
    (hl : w - v = l * (r - u))
    (hn : l * infinityChordDenominator W r v w = infinityChordNumerator W u r v) :
    W.toProjective.addXYZ ![u, 1, v] ![r, 1, w] =
      (r - u) ^ 3 • infinityChord W u v r l := by
  have hr := infinity_line_residual W hl hn
  have hw : w = v + l * (r - u) := by linear_combination hl
  subst w
  rw [equation_iff_cubicForm] at hP
  rw [projective_addXYZ_polar]
  unfold infinityChord
  rw [← Projective.neg_smul]
  congr 1
  ext i
  fin_cases i
  · dsimp [cubicPolar, infinityChordParameter]
    dsimp [cubicForm] at hP
    dsimp [infinityLineLinear, infinityLineQuadratic, infinityLineCubic] at hr ⊢
    linear_combination 3 * (r - u) * hP + (r - u) * (r - 2 * u) * hr
  · dsimp [cubicPolar, infinityChordParameter]
    dsimp [cubicForm] at hP
    dsimp [infinityLineLinear, infinityLineQuadratic, infinityLineCubic] at hr ⊢
    linear_combination -(r - u) * hr
  · dsimp [cubicPolar, infinityChordParameter]
    dsimp [cubicForm] at hP
    dsimp [infinityLineLinear, infinityLineQuadratic, infinityLineCubic] at hr ⊢
    linear_combination 3 * (r - u) * l * hP + (r - u) * ((r - u) * l - v) * hr

theorem infinitySlope_projective_comparison :
    infinitySlopeRestriction W ∘ chartPairSum W true true =
      (fun i ↦ (infinitySlopeCoord W true 0 - infinitySlopeCoord W false 0) ^ 3 *
        infinitySumProjective W i) := by
  have hl : infinitySlopeRestriction W ∘ chartPairLeft W true true =
      ![infinitySlopeCoord W false 0, 1, infinitySlopeCoord W false 1] := by
    ext i
    fin_cases i
    · rfl
    · exact (infinitySlopeRestriction W).map_one
    · rfl
  have hr : infinitySlopeRestriction W ∘ chartPairRight W true true =
      ![infinitySlopeCoord W true 0, 1, infinitySlopeCoord W true 1] := by
    ext i
    fin_cases i
    · rfl
    · exact (infinitySlopeRestriction W).map_one
    · rfl
  have h := Projective.baseChange_addXYZ (W' := W.toProjective) (infinitySlopeRestriction W)
    (chartPairLeft W true true) (chartPairRight W true true)
  rw [hl, hr] at h
  exact h.symm.trans (projective_addXYZ_infinityChord _
    (infinitySlope_input_equation W false) (infinitySlope_relation W) (infinitySlope_normal W))

theorem infinityAdditionSum_normalized (i : Fin 3) :
    chartPointCoords W true (infinityAdditionSum W) i =
      infinityAdditionRestriction W (infinitySumProjective W i) * infinityAdditionInv W := by
  fin_cases i
  · exact infinityAdditionSum_coord W 0
  · exact (IsLocalization.Away.mul_invSelf
      (S := InfinityAdditionRing W) (infinitySumProjective W 1)).symm
  · exact infinityAdditionSum_coord W 1

theorem infinityAdditionSum_normalized_map {S : Type u} [CommRing S] [Algebra R S]
    (f : InfinityAdditionRing W →ₐ[R] S) (i : Fin 3) :
    chartPointCoords W true (f.comp (infinityAdditionSum W)) i =
      f (infinityAdditionRestriction W (infinitySumProjective W i)) *
        f (infinityAdditionInv W) := by
  rw [chartPointCoords_baseChange]
  change f (chartPointCoords W true (infinityAdditionSum W) i) = _
  rw [infinityAdditionSum_normalized, map_mul]

/-- The infinity chord and the projective secant give the same scheme morphism
on every common domain of definition, with either projective output chart. -/
theorem infinity_projective_addition_agreement {S : Type u} [CommRing S] [Algebra R S]
    (d : Bool) (f : InfinityAdditionRing W →ₐ[R] S)
    (g : ProjectiveAdditionRing W true true d →ₐ[R] S)
    (h : f.comp ((infinityAdditionRestriction W).comp (infinitySlopeRestriction W)) =
      g.comp (projectiveAdditionRestriction W true true d)) :
    Spec.map (CommRingCat.ofHom (f.comp (infinityAdditionSum W)).toRingHom) ≫ infinityChart W =
      Spec.map (CommRingCat.ofHom (g.comp (projectiveAdditionSum W true true d)).toRingHom) ≫
        sourceChart W d := by
  let a := f.comp (infinityAdditionRestriction W)
  have hh (i : Fin 3) :
      g (projectiveAdditionRestriction W true true d (chartPairSum W true true i)) =
        a ((infinitySlopeCoord W true 0 - infinitySlopeCoord W false 0) ^ 3) *
          a (infinitySumProjective W i) := by
    have he := DFunLike.congr_fun h (chartPairSum W true true i)
    change a (infinitySlopeRestriction W (chartPairSum W true true i)) =
      g (projectiveAdditionRestriction W true true d (chartPairSum W true true i)) at he
    have hc := congrArg a (congrFun (infinitySlope_projective_comparison W) i)
    simp only [Function.comp_apply, map_mul] at hc
    exact he.symm.trans hc
  apply chart_point_agreement_of_scaled W true d _ _
    (fun i ↦ a (infinitySumProjective W i))
    (fun i ↦ g (projectiveAdditionRestriction W true true d (chartPairSum W true true i)))
    (f (infinityAdditionInv W)) (g (projectiveAdditionInv W true true d))
    (infinityAdditionSum_normalized_map W f)
    (projectiveAdditionSum_normalized_map W true true d g)
  intro i j
  rw [hh, hh]
  ring

end WeierstrassCurve.CubicCharts
