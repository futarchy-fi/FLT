/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.HopfTorsor
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic

/-!
# Descent of surjectivity from Hopf kernels

Over a common Hopf quotient, a morphism surjective on kernel coordinates is
surjective after faithfully flat base change, hence is itself surjective.
-/

@[expose] public noncomputable section

open scoped TensorProduct
open Algebra.TensorProduct WithConv

namespace HopfAlgebra

variable {R B C A : Type*} [CommRing R] [CommRing B] [CommRing C] [CommRing A]
  [HopfAlgebra R B] [HopfAlgebra R C] [HopfAlgebra R A]
  [Algebra B C] [Algebra B A] [IsScalarTower R B C] [IsScalarTower R B A]

/-- A morphism over a common quotient induces a morphism on kernel coordinates. -/
def kernelMap (k : B →ₐc[R] C) (f : B →ₐc[R] A) (g : C →ₐc[R] A)
    (hc : g.comp k = f) : (C ⧸ augmentationIdeal k) →ₐ[R] (A ⧸ augmentationIdeal f) :=
  Ideal.Quotient.liftₐ _ ((Ideal.Quotient.mkₐ R (augmentationIdeal f)).comp g.toAlgHom) (by
    change augmentationIdeal k ≤ RingHom.ker
      (((Ideal.Quotient.mkₐ R (augmentationIdeal f)).comp g.toAlgHom).toRingHom)
    apply Ideal.map_le_iff_le_comap.mpr
    intro b hb
    change Ideal.Quotient.mk (augmentationIdeal f) (g (k b)) = 0
    rw [show g (k b) = f b from DFunLike.congr_fun hc b]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_map_of_mem _ hb))

/-- Torsor trivialization commutes with a morphism over the quotient. -/
theorem torsorHom_naturality
    (k : B →ₐc[R] C) (hk : k.toAlgHom = IsScalarTower.toAlgHom R B C)
    (f : B →ₐc[R] A) (hf : f.toAlgHom = IsScalarTower.toAlgHom R B A)
    (g : C →ₐc[R] A) (hc : g.comp k = f)
    (gB : C →ₐ[B] A) (hgB : gB.restrictScalars R = g.toAlgHom) :
    ((torsorHom f hf).restrictScalars R).comp
        ((Algebra.TensorProduct.map gB gB).restrictScalars R) =
      (Algebra.TensorProduct.map g.toAlgHom (kernelMap k f g hc)).comp
        ((torsorHom k hk).restrictScalars R) := by
  have hco : (torsorCoaction f).comp g.toAlgHom =
      (Algebra.TensorProduct.map g.toAlgHom (kernelMap k f g hc)).comp
        (torsorCoaction k) := by
    rw [torsorCoaction_eq_conv, torsorCoaction_eq_conv,
      AlgHom.convMul_comp_bialgHom_distrib, AlgHom.comp_convMul_distrib]
    congr 2 <;> ext c <;> simp [kernelMap]
    rfl
  apply AlgHom.ext
  intro z
  induction z using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul c d =>
      have hd := AlgHom.congr_fun hco d
      simp only [AlgHom.comp_apply] at hd
      change torsorHom f hf (gB c ⊗ₜ[B] gB d) =
        Algebra.TensorProduct.map g.toAlgHom (kernelMap k f g hc)
          (torsorHom k hk (c ⊗ₜ[B] d))
      simp only [torsorHom, lift_tmul, map_mul, Algebra.ofId_apply, algebraMap_apply,
        map_tmul, map_one]
      change (gB c ⊗ₜ[R] 1) * torsorCoaction f (gB d) =
        (g c ⊗ₜ[R] 1) *
          Algebra.TensorProduct.map g.toAlgHom (kernelMap k f g hc) (torsorCoaction k d)
      have hg (x : C) : gB x = g x := AlgHom.congr_fun hgB x
      rw [hg c, hg d]
      exact congrArg (fun z ↦ (g c ⊗ₜ[R] 1) * z) hd

/-- Faithful flatness over the quotient descends surjectivity from the kernel.
The fibre hypothesis concerns the actual augmentation quotient. -/
theorem surjective_of_kernel_of_faithfullyFlat [Module.FaithfullyFlat B A]
    (k : B →ₐc[R] C) (hk : k.toAlgHom = IsScalarTower.toAlgHom R B C)
    (f : B →ₐc[R] A) (hf : f.toAlgHom = IsScalarTower.toAlgHom R B A)
    (g : C →ₐc[R] A) (hc : g.comp k = f)
    (hs : Function.Surjective
      ((Ideal.Quotient.mkₐ R (augmentationIdeal f)).comp g.toAlgHom)) :
    Function.Surjective g := by
  let gB : C →ₐ[B] A :=
    { __ := g.toAlgHom.toRingHom
      commutes' b := by
        change g (algebraMap B C b) = algebraMap B A b
        rw [← IsScalarTower.toAlgHom_apply R B C, ← hk,
          ← IsScalarTower.toAlgHom_apply R B A, ← hf]
        exact DFunLike.congr_fun hc b }
  let t : A ⊗[B] C →ₐ[A] A ⊗[B] A :=
    lift (Algebra.ofId A _) (includeRight.comp gB) (fun _ _ ↦ .all ..)
  let s : C ⊗[B] C →ₐ[B] A ⊗[B] C :=
    Algebra.TensorProduct.map gB (AlgHom.id B C)
  let v : A ⊗[B] C →ₐ[A] A ⊗[R] (A ⧸ augmentationIdeal f) :=
    (torsorHom f hf).comp t
  have hnat (z : C ⊗[B] C) : v (s z) =
      Algebra.TensorProduct.map g.toAlgHom (kernelMap k f g hc) (torsorHom k hk z) := by
    have hts : t (s z) = Algebra.TensorProduct.map gB gB z := by
      induction z using TensorProduct.inductionOn with
      | tmul c d => simp [t, s]
      | add x y hx hy => simp only [map_add, hx, hy]
    change torsorHom f hf (t (s z)) = _
    rw [hts]
    exact AlgHom.congr_fun (torsorHom_naturality k hk f hf g hc gB rfl) z
  have hv : Function.Surjective v := by
    intro z
    induction z using TensorProduct.inductionOn with
    | add x y hx hy =>
      obtain ⟨x', rfl⟩ := hx
      obtain ⟨y', rfl⟩ := hy
      exact ⟨x' + y', map_add v x' y'⟩
    | tmul a h =>
      obtain ⟨c, hc'⟩ := hs h
      let w := (torsorEquiv k hk).symm
        (1 ⊗ₜ[R] Ideal.Quotient.mk (augmentationIdeal k) c)
      have hw : v (s w) = 1 ⊗ₜ[R] h := by
        rw [hnat]
        change Algebra.TensorProduct.map g.toAlgHom (kernelMap k f g hc)
          (torsorEquiv k hk ((torsorEquiv k hk).symm _)) = _
        rw [AlgEquiv.apply_symm_apply, map_tmul, map_one]
        exact congrArg (fun h ↦ (1 : A) ⊗ₜ[R] h) hc'
      refine ⟨a • s w, ?_⟩
      rw [map_smul, hw]
      exact TensorProduct.smul_tmul' a 1 h |>.trans (by rw [smul_eq_mul, mul_one])
  have ht : Function.Surjective t := by
    intro z
    obtain ⟨w, hw⟩ := hv (torsorHom f hf z)
    exact ⟨w, (torsorEquiv f hf).injective hw⟩
  apply (Module.FaithfullyFlat.lTensor_surjective_iff_surjective B A gB.toLinearMap).mp
  have he : gB.toLinearMap.lTensor A = t.toLinearMap.restrictScalars B := by
    ext a c
    simp [t]
  rw [he]
  exact ht

end HopfAlgebra
