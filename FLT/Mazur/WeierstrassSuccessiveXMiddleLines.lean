/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSuccessiveXMiddleConic

/-!
# The two actual attached lines of the successive middle fiber

For either tangent root r, setting t = 0 and v = r leaves the retained
horizontal coordinate u free. The exact kernel is (t,v-r).
-/

@[expose] public noncomputable section
open Polynomial
namespace FLT.Mazur.WeierstrassSuccessiveX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) (c : R) (h2 : W.a₂ = 0)
  (r : R) (hr : r * (r + W.a₁) = 0)
local notation "A" => Coordinate W 0 0 0 0 c
local notation "T" => coord W 0 0 0 0 c 0
local notation "V" => coord W 0 0 0 0 c 1
local notation "U" => coord W 0 0 0 0 c 2

/-- Restrict the middle fiber to the horizontal line with the specified tangent root. -/
def middleLineMap : A →ₐ[R] R[X] :=
  evaluation W 0 0 0 0 c ![0, C r, X] (by
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, h2, map_zero,
      zero_mul, add_zero, zero_pow (by decide : 2 ≠ 0), mul_zero]
    have h := congrArg (C : R →+* R[X]) hr
    simp only [map_mul, map_add, map_zero] at h
    change C r ^ 2 + C W.a₁ * C r = 0
    linear_combination h) (by simp)

/-- The line map keeps u as its free coordinate and retains the specified slope. -/
@[simp] theorem middleLineMap_coord (i : Fin 3) :
    middleLineMap W c h2 r hr (coord W 0 0 0 0 c i) = ![0, C r, X] i :=
  evaluation_coord _ _ _ _ _ _ _ _ _ i

/-- Every polynomial horizontal function is the restriction of an actual fiber function. -/
theorem middleLineMap_surjective : Function.Surjective (middleLineMap W c h2 r hr) := by
  intro p
  refine ⟨aeval U p, ?_⟩
  rw [← aeval_algHom_apply, middleLineMap_coord]
  exact aeval_X_left_apply p

/-- The actual ideal cutting out the specified horizontal tangent line. -/
def middleLineIdeal : Ideal A := Ideal.span {T, V - algebraMap R A r}

/-- The original two equations are the entire kernel of the line restriction. -/
theorem middleLineMap_ker : RingHom.ker (middleLineMap W c h2 r hr) =
    middleLineIdeal W c r := by
  let I : Ideal A := middleLineIdeal W c r
  let q := Ideal.Quotient.mkₐ R I
  have ht : q T = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr
    (Ideal.subset_span (Set.mem_insert _ _))
  have hv : q V = q (algebraMap R A r) := by
    have h : q (V - algebraMap R A r) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr
      (Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _)))
    simpa only [map_sub, AlgHom.commutes, sub_eq_zero] using h
  have he : (aeval (q U)).comp (middleLineMap W c h2 r hr) = q := by
    refine hom_ext W 0 0 0 0 c (S := A ⧸ I) _ _ ?_
    intro i
    fin_cases i <;> simp [AlgHom.comp_apply, ht, hv]
  refine le_antisymm ?_ ?_
  · intro z hz
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    have hz' : middleLineMap W c h2 r hr z = 0 := hz
    simpa only [AlgHom.comp_apply, hz', map_zero, q, I, Ideal.Quotient.mkₐ_eq_mk]
      using (DFunLike.congr_fun he z).symm
  · rw [middleLineIdeal, Ideal.span_le]
    intro z hz
    rcases Set.mem_insert_iff.mp hz with rfl | hz
    · exact middleLineMap_coord W c h2 r hr 0
    · obtain rfl := Set.mem_singleton_iff.mp hz
      change middleLineMap W c h2 r hr (V - algebraMap R A r) = 0
      simp

/-- The ordered first tangent is zero. -/
theorem middle_first_root : (0 : R) * (0 + W.a₁) = 0 := zero_mul _

/-- The ordered second tangent is minus the original tangent coefficient. -/
theorem middle_second_root : (-W.a₁) * (-W.a₁ + W.a₁) = 0 := by simp

end FLT.Mazur.WeierstrassSuccessiveX
