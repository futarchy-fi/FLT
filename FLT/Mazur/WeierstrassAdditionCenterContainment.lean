/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationCenterCharts
public import FLT.Mazur.WeierstrassOrdinaryCenterIdeal
public import FLT.Mazur.WeierstrassReciprocalSingularCenter
public import FLT.Mazur.WeierstrassProjectiveCenterIdeal

/-!
# Pullback containment of full center ideals on the actual addition presentations

These are comparisons of the extended ideals themselves, not merely their
vanishing sets. The statements allow every coefficient algebra, so they can
be applied after restricting any of the genuine smooth-input covers.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
  (W : WeierstrassCurve R) (s : R)

/-- Comparing an extended center ideal amounts to its three original generators. -/
theorem modificationChartCenter_map_le_iff (j : Fin 3)
    (f : Coordinate W j →ₐ[R] S) (I : Ideal S) :
    (modificationChartCenter W s j).map f.toRingHom ≤ I ↔
      algebraMap R S s ∈ I ∧ f (coord W j 0) ∈ I ∧ f (coord W j 1) ∈ I := by
  rw [modificationChartCenter_map]
  simp only [Ideal.span_insert, sup_le_iff, Ideal.span_singleton_le_iff_mem]

/-- Both ordinary addition maps pull the output center into the unchanged input center. -/
theorem ordinarySpecialization_center_le (b : Bool)
    (f : additionChartRing W (ordinaryIndex b) →ₐ[R] S) (b3 b4 : R)
    (h3 : W.a₃ = s * b3) (h4 : W.a₄ = s * b4) :
    (modificationChartCenter W s 2).map (f.comp (ordinaryChartAddition W b)).toRingHom ≤
      (modificationChartCenter W s 2).map (f.comp (ordinaryInputRight W b)).toRingHom := by
  rw [modificationChartCenter_map_le_iff, modificationChartCenter_map]
  exact ⟨Ideal.subset_span (by simp),
    ordinarySpecialization_modificationCenter W b f s b3 b4 h3 h4⟩

/-- Both reciprocal presentations have unit input center, just like their output-Y chart. -/
theorem reciprocalSpecialization_modificationCenter_eq_top (b : Bool)
    (f : additionChartRing W (reciprocalIndex b) →ₐ[R] S) (b3 b4 : R)
    (h3 : W.a₃ = s * b3) (h4 : W.a₄ = s * b4) :
    (modificationChartCenter W s 2).map (f.comp (reciprocalInputRight W b)).toRingHom =
      ⊤ := by
  rw [modificationChartCenter_map]
  apply reciprocalSpecialization_center_eq_top W b f
  · rw [h3, map_mul]
    exact Ideal.mul_mem_right _ _ (Ideal.subset_span (by simp))
  · rw [h4, map_mul]
    exact Ideal.mul_mem_right _ _ (Ideal.subset_span (by simp))
  · exact Ideal.subset_span (by simp)
  · exact Ideal.subset_span (by simp)

/-- Reciprocal addition satisfies the same full ideal containment as ordinary addition. -/
theorem reciprocalSpecialization_center_le (b : Bool)
    (f : additionChartRing W (reciprocalIndex b) →ₐ[R] S) (b3 b4 : R)
    (h3 : W.a₃ = s * b3) (h4 : W.a₄ = s * b4) :
    (modificationChartCenter W s 1).map (f.comp (reciprocalChartAddition W b)).toRingHom ≤
      (modificationChartCenter W s 2).map (f.comp (reciprocalInputRight W b)).toRingHom := by
  rw [reciprocalSpecialization_modificationCenter_eq_top W s b f b3 b4 h3 h4]
  exact le_top

/-- Every actual polynomial presentation has the required full center containment. -/
theorem projectiveSpecialization_center_le (j k t : Fin 3)
    (f : AdditionOutputOpen W j k t →ₐ[R] S) (b3 b4 b6 : R)
    (h3 : W.a₃ = s * b3) (h4 : W.a₄ = s * b4) (h6 : W.a₆ = s * b6) :
    (modificationChartCenter W s t).map (f.comp (projectiveAdditionChart W j k t)).toRingHom ≤
      (modificationChartCenter W s k).map
        ((f.comp (additionOutputRestriction W j k t)).comp
          (chartProductRight W j k)).toRingHom := by
  rw [modificationChartCenter_map_le_iff, modificationChartCenter_map]
  exact ⟨Ideal.subset_span (by simp),
    projectiveSpecialization_modificationCenter W j k t f s b3 b4 b6 h3 h4 h6⟩

end FLT.Mazur.WeierstrassIntegralChart
