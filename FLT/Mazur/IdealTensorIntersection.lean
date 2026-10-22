/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ModuleIdealTensorFinite
public import Mathlib.LinearAlgebra.TensorProduct.RightExactness

/-!
# Moving an ideal-tensor kernel into an intersection

If multiplication is injective on the tensor of the sum of two ideals,
every kernel element for the first ideal comes from their intersection.
This is the diagram chase needed before Artin-Rees can be applied.
-/

@[expose] public noncomputable section
open TensorProduct
namespace FLT.Mazur.IdealTensorIntersection
variable {R : Type*} [CommRing R]

/-- The signed diagonal from the intersection into the product of ideals. -/
def diagonal (I J : Ideal R) : (I ⊓ J : Ideal R) →ₗ[R] I × J where
  toFun x := (⟨x.val, x.property.1⟩, ⟨-x.val, J.neg_mem x.property.2⟩)
  map_add' x y := by ext <;> simp [add_comm]
  map_smul' a x := by ext <;> simp

/-- Addition maps the product onto the sum of ideals. -/
def addition (I J : Ideal R) : I × J →ₗ[R] (I ⊔ J : Ideal R) where
  toFun x := ⟨x.1.val + x.2.val, Submodule.add_mem_sup x.1.property x.2.property⟩
  map_add' x y := by ext; simp; abel
  map_smul' a x := by ext; simp [mul_add]

/-- This ideal sequence is exact without any flatness assumptions. -/
theorem exact (I J : Ideal R) : Function.Exact (diagonal I J) (addition I J) := by
  intro x
  constructor
  · intro hx
    have he : x.1.val + x.2.val = 0 := congrArg Subtype.val hx
    refine ⟨⟨x.1.val, x.1.property, ?_⟩, ?_⟩
    · rw [eq_neg_of_add_eq_zero_left he]
      exact J.neg_mem x.2.property
    · apply Prod.ext
      · rfl
      · apply Subtype.ext
        exact neg_eq_of_add_eq_zero_right he
  · rintro ⟨y, rfl⟩
    apply Subtype.ext
    exact add_neg_cancel y.val

/-- Tensor right exactness applies because ideal addition is actually onto. -/
theorem addition_surjective (I J : Ideal R) : Function.Surjective (addition I J) := by
  intro x
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp x.property
  exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), Subtype.ext hab⟩

variable {S M : Type*} [CommRing S] [Algebra R S]
  [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]

/-- Injectivity for the larger ideal moves every obstruction into the intersection. -/
theorem kernel_lifts_inf (I J : Ideal R)
    (h : Function.Injective (ModuleIdealTensor.inclusion (S := S) (M := M) (I ⊔ J)))
    (z : M ⊗[R] I) (hz : ModuleIdealTensor.inclusion (S := S) I z = 0) :
    ∃ w : M ⊗[R] (I ⊓ J : Ideal R),
      (Submodule.inclusion inf_le_left).lTensor M w = z := by
  let f := LinearMap.inl R I J
  let p := LinearMap.fst R I J
  have hzero : (addition I J).lTensor M (f.lTensor M z) = 0 := by
    apply h
    rw [map_zero]
    have he (t : M ⊗[R] I) :
        ModuleIdealTensor.inclusion (S := S) (I ⊔ J)
          ((addition I J).lTensor M (f.lTensor M t)) =
        ModuleIdealTensor.inclusion (S := S) I t := by
      induction t with
      | tmul m a => simp [f, addition]
      | add x y hx hy => simp only [map_add, hx, hy]
    rw [he, hz]
  obtain ⟨w, hw⟩ := (lTensor_exact M (exact I J) (addition_surjective I J) _).mp hzero
  refine ⟨w, ?_⟩
  have he : p.comp (diagonal I J) = Submodule.inclusion inf_le_left := rfl
  have hp : p.comp f = LinearMap.id := rfl
  have hh := congrArg (p.lTensor M) hw
  simpa only [← LinearMap.comp_apply, ← LinearMap.lTensor_comp, he, hp, LinearMap.lTensor_id,
    LinearMap.id_apply] using hh

end FLT.Mazur.IdealTensorIntersection
