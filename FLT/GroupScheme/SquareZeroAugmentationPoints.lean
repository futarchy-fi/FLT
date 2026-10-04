/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mathlib.RingTheory.AugmentationTangentEquiv
public import Mathlib.RingTheory.Ideal.Operations

/-! # Actual augmentation points across a square-zero thickening -/

@[expose] public noncomputable section
namespace AlgHom
variable {R A B C : Type*} [CommRing R] [CommRing A] [CommRing B] [CommRing C]
  [Algebra R A] [Algebra R B] [Algebra R C]
  (ε : A →ₐ[R] R) (q : B →ₐ[R] C) (hJ : RingHom.ker q ^ 2 = ⊥)

/-- Points in the actual kernel of reduction at the given augmentation. -/
def AugmentationPointKernel :=
  {f : A →ₐ[R] B // q.comp f = (Algebra.ofId R C).comp ε}

include hJ in
/-- Products in the actual square-zero kernel vanish. -/
theorem squareZeroKernel_mul (a b : RingHom.ker q) : (a : B) * b = 0 := by
  have h := Ideal.mul_mem_mul a.property b.property
  rw [← pow_two, hJ] at h
  exact h

/-- Subtracting the augmentation yields a tangent valued in the actual kernel. -/
def augmentationPointToTangent (f : ε.AugmentationPointKernel q) :
    ε.augmentationTangent (M := RingHom.ker q) := by
  let e : A →ₐ[R] B := (Algebra.ofId R B).comp ε
  have hf (a : A) : f.val a - e a ∈ RingHom.ker q := by
    change q (f.val a - e a) = 0
    rw [map_sub]
    exact sub_eq_zero.mpr ((AlgHom.congr_fun f.property a).trans (q.commutes (ε a)).symm)
  let d : A →ₗ[R] RingHom.ker q :=
    (f.val.toLinearMap - e.toLinearMap).codRestrict
      ((RingHom.ker q).restrictScalars R) hf
  refine ⟨d, fun a b ↦ ?_⟩
  apply Subtype.ext
  change f.val (a * b) - e (a * b) =
    ε a • (f.val b - e b) + ε b • (f.val a - e a)
  simp only [Algebra.smul_def]
  have hz := squareZeroKernel_mul q hJ ⟨_, hf a⟩ ⟨_, hf b⟩
  change (f.val a - e a) * (f.val b - e b) = 0 at hz
  change f.val (a * b) - e (a * b) = e a * (f.val b - e b) + e b * (f.val a - e a)
  rw [map_mul, map_mul]
  calc
    _ = (f.val a - e a) * (f.val b - e b) +
        (e a * (f.val b - e b) + e b * (f.val a - e a)) := by ring
    _ = _ := by rw [hz, zero_add]

/-- Adding a kernel-valued tangent to the augmentation produces an actual point. -/
def tangentToAugmentationPoint (d : ε.augmentationTangent (M := RingHom.ker q)) :
    ε.AugmentationPointKernel q := by
  let e : A →ₐ[R] B := (Algebra.ofId R B).comp ε
  let f : A →ₐ[R] B :=
    { toFun a := e a + d.val a
      map_zero' := by simp
      map_one' := by simp [augmentationTangent_one]
      map_add' := by intro a b; simp only [map_add, Submodule.coe_add]; ring
      map_mul' := by
        intro a b
        have hz := squareZeroKernel_mul q hJ (d.val a) (d.val b)
        have hd := congrArg (fun z : RingHom.ker q ↦ (z : B)) (d.property a b)
        change (d.val (a * b) : B) = ε a • (d.val b : B) + ε b • (d.val a : B) at hd
        simp only [Algebra.smul_def] at hd
        change (d.val (a * b) : B) = e a * d.val b + e b * d.val a at hd
        rw [map_mul, hd]
        calc
          _ = (e a + d.val a) * (e b + d.val b) - (d.val a : B) * d.val b := by ring
          _ = _ := by rw [hz, sub_zero]
      commutes' := by intro r; simp [e, augmentationTangent_algebraMap] }
  refine ⟨f, ?_⟩
  ext a
  change q (e a + d.val a) = algebraMap R C (ε a)
  rw [map_add, show q (d.val a) = 0 from (d.val a).property, add_zero]
  exact q.commutes (ε a)

/-- The infinitesimal kernel is precisely the module of kernel-valued tangent functionals. -/
def augmentationPointKernelEquiv :
    ε.AugmentationPointKernel q ≃ ε.augmentationTangent (M := RingHom.ker q) where
  toFun := augmentationPointToTangent ε q hJ
  invFun := tangentToAugmentationPoint ε q hJ
  left_inv f := by
    apply Subtype.ext
    ext a
    change algebraMap R B (ε a) + (f.val a - algebraMap R B (ε a)) = f.val a
    ring
  right_inv d := by
    apply Subtype.ext
    ext a
    change algebraMap R B (ε a) + (d.val a : B) - algebraMap R B (ε a) = d.val a
    ring

/-- The same kernel is represented by the original augmentation cotangent quotient. -/
def augmentationPointCotangentEquiv :
    ε.AugmentationPointKernel q ≃ ((RingHom.ker ε).Cotangent →ₗ[R] RingHom.ker q) :=
  (augmentationPointKernelEquiv ε q hJ).trans ε.augmentationTangentEquiv.symm.toEquiv

end AlgHom
