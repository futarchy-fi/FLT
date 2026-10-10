/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassReciprocalCubicSpecialization
public import FLT.Mazur.WeierstrassMixedLeftReciprocalInverse
public import FLT.Mazur.WeierstrassMixedRightReciprocalInverse
public import FLT.Mazur.WeierstrassOrdinarySpecializationUnits

/-!
# Mixed outer triple outputs are affine

A reciprocal outer chart opposite an ordinary outer chart has invertible output z.
Only matching input maps are hypotheses; the output unit follows from the scalar identities.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.WeierstrassIntegralChart

open WeierstrassIntegralAddition

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
  (W : WeierstrassCurve R)

/-- The right reciprocal output is affine on every compatible common algebra. -/
theorem mixedRightReciprocalAlgebra_z_isUnit (b c d e : Bool)
    (f : additionChartRing W (ordinaryIndex b) →ₐ[R] S)
    (g : additionChartRing W (ordinaryIndex c) →ₐ[R] S)
    (h : additionChartRing W (ordinaryIndex d) →ₐ[R] S)
    (k : additionChartRing W (reciprocalIndex e) →ₐ[R] S)
    (hmid : f.comp (ordinaryInputRight W b) = g.comp (ordinaryInputLeft W c))
    (hleft : h.comp (ordinaryInputLeft W d) = f.comp (ordinaryChartAddition W b))
    (hthird : h.comp (ordinaryInputRight W d) = g.comp (ordinaryInputRight W c))
    (hfirst : k.comp (reciprocalInputLeft W e) = f.comp (ordinaryInputLeft W b))
    (hright : k.comp (reciprocalInputRight W e) = g.comp (ordinaryChartAddition W c)) :
    IsUnit (k (reciprocalChartAddition W e (coord W 1 2))) := by
  have hm (i) : g (ordinaryInputLeft W c (coord W 2 i)) =
      f (ordinaryInputRight W b (coord W 2 i)) :=
    (DFunLike.congr_fun hmid (coord W 2 i)).symm
  have hl (i) : h (ordinaryInputLeft W d (coord W 2 i)) =
      f (ordinaryChartAddition W b (coord W 2 i)) := DFunLike.congr_fun hleft _
  have ht (i) : h (ordinaryInputRight W d (coord W 2 i)) =
      g (ordinaryInputRight W c (coord W 2 i)) := DFunLike.congr_fun hthird _
  have hf (i) : k (reciprocalInputLeft W e (coord W 2 i)) =
      f (ordinaryInputLeft W b (coord W 2 i)) := DFunLike.congr_fun hfirst _
  have hr (i) : k (reciprocalInputRight W e (coord W 2 i)) =
      g (ordinaryChartAddition W c (coord W 2 i)) := DFunLike.congr_fun hright _
  have h₁ := ordinarySpecialization_line W b f
  have h₂ := ordinarySpecialization_line W c g
  have hc₁ := ordinarySpecialization_cubic W b f
  have hc₂ := ordinarySpecialization_cubic W c g
  dsimp only at hc₁ hc₂
  rw [hm 0, hm 1] at h₂ hc₂
  have hn := ordinarySpecialization_line W d h
  have ho := reciprocalSpecialization_line W e k
  have hd := ordinarySpecialization_denominator_unit W d h
  have he := reciprocalSpecialization_denominator_unit W e k
  have hnc := ordinarySpecialization_cubic W d h
  have hoc := reciprocalSpecialization_cubic W e k
  dsimp only at hnc hoc hd he
  simp only [hl, ht, ordinarySpecialization_coord, Matrix.cons_val_zero,
    Matrix.cons_val_one] at hn hnc hd
  simp only [hf, hr, ordinarySpecialization_coord, Matrix.cons_val_zero,
    Matrix.cons_val_one, hm] at ho hoc he
  apply (reciprocalSpecialization_z_isUnit_iff W e k).mpr
  apply isUnit_iff_exists_inv.mpr
  refine ⟨_, mixed_right_reciprocal_inverse (W.map (algebraMap R S))
    h₁ h₂ hc₁ hc₂ hn ho hnc hoc hd he⟩

/-- The left reciprocal output is affine on every compatible common algebra. -/
theorem mixedLeftReciprocalAlgebra_z_isUnit (b c d e : Bool)
    (f : additionChartRing W (ordinaryIndex b) →ₐ[R] S)
    (g : additionChartRing W (ordinaryIndex c) →ₐ[R] S)
    (h : additionChartRing W (reciprocalIndex d) →ₐ[R] S)
    (k : additionChartRing W (ordinaryIndex e) →ₐ[R] S)
    (hmid : f.comp (ordinaryInputRight W b) = g.comp (ordinaryInputLeft W c))
    (hleft : h.comp (reciprocalInputLeft W d) = f.comp (ordinaryChartAddition W b))
    (hthird : h.comp (reciprocalInputRight W d) = g.comp (ordinaryInputRight W c))
    (hfirst : k.comp (ordinaryInputLeft W e) = f.comp (ordinaryInputLeft W b))
    (hright : k.comp (ordinaryInputRight W e) = g.comp (ordinaryChartAddition W c)) :
    IsUnit (h (reciprocalChartAddition W d (coord W 1 2))) := by
  have hm (i) : g (ordinaryInputLeft W c (coord W 2 i)) =
      f (ordinaryInputRight W b (coord W 2 i)) :=
    (DFunLike.congr_fun hmid (coord W 2 i)).symm
  have hl (i) : h (reciprocalInputLeft W d (coord W 2 i)) =
      f (ordinaryChartAddition W b (coord W 2 i)) := DFunLike.congr_fun hleft _
  have ht (i) : h (reciprocalInputRight W d (coord W 2 i)) =
      g (ordinaryInputRight W c (coord W 2 i)) := DFunLike.congr_fun hthird _
  have hf (i) : k (ordinaryInputLeft W e (coord W 2 i)) =
      f (ordinaryInputLeft W b (coord W 2 i)) := DFunLike.congr_fun hfirst _
  have hr (i) : k (ordinaryInputRight W e (coord W 2 i)) =
      g (ordinaryChartAddition W c (coord W 2 i)) := DFunLike.congr_fun hright _
  have h₁ := ordinarySpecialization_line W b f
  have h₂ := ordinarySpecialization_line W c g
  have hc₁ := ordinarySpecialization_cubic W b f
  have hc₂ := ordinarySpecialization_cubic W c g
  dsimp only at hc₁ hc₂
  rw [hm 0, hm 1] at h₂ hc₂
  have hn := reciprocalSpecialization_line W d h
  have ho := ordinarySpecialization_line W e k
  have hd := reciprocalSpecialization_denominator_unit W d h
  have he := ordinarySpecialization_denominator_unit W e k
  have hnc := reciprocalSpecialization_cubic W d h
  have hoc := ordinarySpecialization_cubic W e k
  dsimp only at hnc hoc hd he
  simp only [hl, ht, ordinarySpecialization_coord, Matrix.cons_val_zero,
    Matrix.cons_val_one] at hn hnc hd
  simp only [hf, hr, ordinarySpecialization_coord, Matrix.cons_val_zero,
    Matrix.cons_val_one, hm] at ho hoc he
  apply (reciprocalSpecialization_z_isUnit_iff W d h).mpr
  apply isUnit_iff_exists_inv.mpr
  refine ⟨_, mixed_left_reciprocal_inverse (W.map (algebraMap R S))
    h₁ h₂ hc₁ hc₂ hn ho hnc hoc hd he⟩

end FLT.Mazur.WeierstrassIntegralChart
