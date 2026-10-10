/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSuccessiveXAlgebra
public import FLT.Mazur.WeierstrassModificationXFiberConic

/-!
# The retained conic in the successive middle fiber

Setting u to zero gives the original conic, with its full coefficient c.
The conic also maps back by its two actual generators; its restriction is
surjective and has exactly the principal ideal (u) as kernel.
-/

@[expose] public noncomputable section
open FLT.Mazur.WeierstrassModificationX
namespace FLT.Mazur.WeierstrassSuccessiveX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) (c : R) (h2 : W.a₂ = 0)
local notation "A" => Coordinate W 0 0 0 0 c
local notation "T" => coord W 0 0 0 0 c 0
local notation "V" => coord W 0 0 0 0 c 1
local notation "U" => coord W 0 0 0 0 c 2

include h2 in
/-- The full middle fiber satisfies the conic equation before imposing u = 0. -/
theorem middle_conic_relation : V * (V + algebraMap R A W.a₁) -
    algebraMap R A c * T ^ 2 = 0 := by
  have h := equation W 0 0 0 0 c
  simp only [h2, map_zero, zero_mul, zero_add, add_zero] at h
  linear_combination h

/-- Restrict the full successive middle fiber to its conic component. -/
def middleConicMap : A →ₐ[R] ConicCoordinate W.a₁ c :=
  evaluation W 0 0 0 0 c ![conicT W.a₁ c, conicV W.a₁ c, 0] (by
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, h2, map_zero,
      zero_mul, zero_add, add_zero]
    linear_combination conic_relation W.a₁ c) (by simp)

/-- Conic restriction retains both conic coordinates and sets only u to zero. -/
@[simp] theorem middleConicMap_coord (i : Fin 3) :
    middleConicMap W c h2 (coord W 0 0 0 0 c i) = ![conicT W.a₁ c, conicV W.a₁ c, 0] i :=
  evaluation_coord _ _ _ _ _ _ _ _ _ i

/-- The actual conic generators give a section of conic restriction. -/
def middleConicSection : ConicCoordinate W.a₁ c →ₐ[R] A :=
  conicEvaluation W.a₁ c T V (middle_conic_relation W c h2)

/-- The section keeps t. -/
@[simp] theorem middleConicSection_t : middleConicSection W c h2 (conicT W.a₁ c) = T :=
  conicEvaluation_t _ _ _ _ _

/-- The section keeps v. -/
@[simp] theorem middleConicSection_v : middleConicSection W c h2 (conicV W.a₁ c) = V :=
  conicEvaluation_v _ _ _ _ _

/-- Conic restriction followed by the actual section is the identity. -/
theorem middleConicMap_section :
    (middleConicMap W c h2).comp (middleConicSection W c h2) = AlgHom.id R _ := by
  apply conic_hom_ext <;> simp

/-- Every conic function extends to the full middle fiber. -/
theorem middleConicMap_surjective : Function.Surjective (middleConicMap W c h2) := by
  intro z
  exact ⟨middleConicSection W c h2 z, DFunLike.congr_fun (middleConicMap_section W c h2) z⟩

/-- The conic restriction has exactly the original horizontal principal ideal as kernel. -/
theorem middleConicMap_ker : RingHom.ker (middleConicMap W c h2) = Ideal.span {U} := by
  let I : Ideal A := Ideal.span {U}
  let q := Ideal.Quotient.mkₐ R I
  have hu : q U = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr
    (Ideal.subset_span (Set.mem_singleton _))
  have he : (q.comp (middleConicSection W c h2)).comp (middleConicMap W c h2) = q := by
    refine hom_ext W 0 0 0 0 c (S := A ⧸ I) _ _ ?_
    intro i
    fin_cases i <;> simp [AlgHom.comp_apply, hu]
  refine le_antisymm ?_ ?_
  · intro z hz
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    have hz' : middleConicMap W c h2 z = 0 := hz
    simpa only [AlgHom.comp_apply, hz', map_zero, q, I, Ideal.Quotient.mkₐ_eq_mk]
      using (DFunLike.congr_fun he z).symm
  · rw [Ideal.span_le, Set.singleton_subset_iff]
    exact middleConicMap_coord W c h2 2

end FLT.Mazur.WeierstrassSuccessiveX
