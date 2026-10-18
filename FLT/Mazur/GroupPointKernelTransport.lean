/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.CategoryTheory.Monoidal.Cartesian.CommGrp_

/-!
# Transporting group-point kernels through an isomorphism of test objects

Changing the presentation of a test object preserves the actual restriction
kernel and its power-map bijectivity.
-/

@[expose] public noncomputable section
open CategoryTheory MonObj
namespace FLT.Mazur.GroupPointKernelTransport

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {C : Type*} [Category C] [CartesianMonoidalCategory C] [BraidedCategory C]
  {A B T G : C} [CommGrpObj G]

/-- Restriction of points of a commutative group object. -/
def restriction (r : T ⟶ B) : (B ⟶ G) →* (T ⟶ G) where
  toFun z := r ≫ z
  map_one' := comp_one r
  map_mul' := comp_mul r

/-- A test-object isomorphism induces a group isomorphism on points. -/
def pointEquiv (e : A ≅ B) : (B ⟶ G) ≃* (A ⟶ G) where
  toFun z := e.hom ≫ z
  invFun z := e.inv ≫ z
  left_inv z := by simp only [← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  right_inv z := by simp only [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
  map_mul' a b := comp_mul e.hom a b

variable (e : A ≅ B) (q : T ⟶ A) (r : T ⟶ B) (hqr : q ≫ e.hom = r)

include hqr in
/-- Compatibility with the original test map retains exactly the same reduced point. -/
theorem restriction_pointEquiv (z : B ⟶ G) :
    restriction q (pointEquiv (G := G) e z) = restriction r z := by
  change q ≫ (e.hom ≫ z) = r ≫ z
  rw [← Category.assoc, hqr]

/-- The isomorphism on points restricts to the actual reduction kernels. -/
def kernelEquiv : (restriction (G := G) r).ker ≃* (restriction (G := G) q).ker where
  toFun z := ⟨pointEquiv (G := G) e z.val, by
    rw [MonoidHom.mem_ker, restriction_pointEquiv (G := G) e q r hqr]
    exact z.property⟩
  invFun z := ⟨(pointEquiv (G := G) e).symm z, by
    rw [MonoidHom.mem_ker, ← restriction_pointEquiv (G := G) e q r hqr,
      (pointEquiv (G := G) e).apply_symm_apply]
    exact z.property⟩
  left_inv z := Subtype.ext ((pointEquiv (G := G) e).symm_apply_apply z.val)
  right_inv z := Subtype.ext ((pointEquiv (G := G) e).apply_symm_apply z.val)
  map_mul' a b := by
    apply Subtype.ext
    exact (pointEquiv (G := G) e).map_mul a.val b.val

include hqr in
/-- Kernel-power bijectivity is unchanged by the test-object identification. -/
theorem kernel_pow_bijective (n : ℕ)
    (h : Function.Bijective (fun z : (restriction (G := G) r).ker ↦ z ^ n)) :
    Function.Bijective (fun z : (restriction (G := G) q).ker ↦ z ^ n) := by
  let E := kernelEquiv (G := G) e q r hqr
  constructor
  · intro a b hab
    apply E.symm.injective
    apply h.1
    exact (map_pow E.symm a n).symm.trans
      ((congrArg E.symm hab).trans (map_pow E.symm b n))
  · intro b
    obtain ⟨a, ha⟩ := h.2 (E.symm b)
    exact ⟨E a, (map_pow E a n).symm.trans ((congrArg E ha).trans (E.apply_symm_apply b))⟩

end FLT.Mazur.GroupPointKernelTransport
