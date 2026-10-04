/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.RaynaudKernelExactness
public import FLT.GroupScheme.HopfTorsor

/-! # Generic points of the actual augmentation ideal -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped TensorProduct
namespace ThreeAdicPlan
variable {R K : Type} [CommRing R] [Field K] [Algebra R K]
  {X Y Z : FF R K}

/-- Augmentation ideals pull back along composition of the actual maps. -/
theorem ModelHom.augmentationIdeal_comp (f : ModelHom X Y) (g : ModelHom Y Z) :
    HopfAlgebra.augmentationIdeal (f.comp g) =
      (HopfAlgebra.augmentationIdeal g).map f.toAlgHom.toRingHom :=
  (Ideal.map_map g.toAlgHom.toRingHom f.toAlgHom.toRingHom).symm

/-- Vanishing of the actual augmentation ideal detects the kernel on generic points. -/
theorem ModelHom.genericHom_eq_zero_iff_vanish (f : ModelHom X Y)
    (u : K ⊗[R] X.CoordinateRing →ₐ[K] AlgebraicClosure K) :
    genericHom f (X.points (Additive.ofMul u)) = 0 ↔
      ∀ a ∈ HopfAlgebra.augmentationIdeal f, u (1 ⊗ₜ[R] a) = 0 := by
  let t := Bialgebra.restrictPoints R K (AlgebraicClosure K) X.CoordinateRing u
  rw [f.genericHom_eq_zero_iff_counit]
  constructor
  · intro h
    have hi : HopfAlgebra.augmentationIdeal f ≤ RingHom.ker t.toRingHom := by
      apply Ideal.map_le_iff_le_comap.mpr
      intro a ha
      change t (f a) = 0
      have he : Coalgebra.counit (R := R) a = 0 := ha
      exact (h a).trans (by rw [he, map_zero])
    exact fun a ha ↦ hi ha
  · intro h a
    let ε := Bialgebra.counitAlgHom R Y.CoordinateRing
    have ha : a - algebraMap R Y.CoordinateRing (ε a) ∈ RingHom.ker ε.toRingHom := by
      change ε (a - algebraMap R Y.CoordinateRing (ε a)) = 0
      simp only [map_sub, ε.commutes, Algebra.algebraMap_self, RingHom.id_apply, sub_self]
    have he := h _ (Ideal.mem_map_of_mem f.toAlgHom.toRingHom ha)
    change (t.comp f.toAlgHom) (a - algebraMap R Y.CoordinateRing (ε a)) = 0 at he
    rw [map_sub, AlgHom.commutes, sub_eq_zero] at he
    exact he

/-- Equal integral augmentation ideals give equal kernels on the original generic points. -/
theorem ModelHom.genericHom_eq_zero_iff_of_augmentation_eq
    (f : ModelHom X Y) (g : ModelHom X Z)
    (h : HopfAlgebra.augmentationIdeal f = HopfAlgebra.augmentationIdeal g) (x : X.Points) :
    genericHom f x = 0 ↔ genericHom g x = 0 := by
  obtain ⟨u, rfl⟩ := X.points_bijective.2 x
  have hf := f.genericHom_eq_zero_iff_vanish u.toMul
  have hg := g.genericHom_eq_zero_iff_vanish u.toMul
  rw [h] at hf
  exact hf.trans hg.symm
end ThreeAdicPlan
