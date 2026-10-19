/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Affine

/-!
# Lifting exact boundary kernels through affine closed restrictions

In a cartesian square of affine closed subschemes, every coefficient that
vanishes on the restricted boundary lifts to a coefficient vanishing on the
original boundary. The proof keeps the entire defining ideals, including
nilpotents, by computing the kernel in the actual ring pushout.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.AffineClosedBoundaryKernelLifting
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-- A surjective side of a ring pushout gives the exact extended boundary ideal. -/
theorem pushout_kernel {R A B C : CommRingCat}
    {f : R ⟶ A} {g : R ⟶ B} {i : A ⟶ C} {j : B ⟶ C}
    (H : IsPushout f g i j) (hf : Function.Surjective f) :
    RingHom.ker j.hom = (RingHom.ker f.hom).map g.hom := by
  let J := (RingHom.ker f.hom).map g.hom
  let q : B ⟶ CommRingCat.of (B ⧸ J) := CommRingCat.ofHom (Ideal.Quotient.mk J)
  have hk : RingHom.ker f.hom ≤ RingHom.ker (q.hom.comp g.hom) := by
    intro r hr
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_map_of_mem g.hom hr)
  let l : A ⟶ CommRingCat.of (B ⧸ J) :=
    CommRingCat.ofHom (RingHom.liftOfSurjective f.hom hf ⟨q.hom.comp g.hom, hk⟩)
  have hl : f ≫ l = g ≫ q := by
    ext r
    exact RingHom.liftOfSurjective_comp_apply f.hom hf ⟨q.hom.comp g.hom, hk⟩ r
  let d : C ⟶ CommRingCat.of (B ⧸ J) := H.desc l q hl
  have hd : j ≫ d = q := H.inr_desc l q hl
  apply le_antisymm
  · intro x hx
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    have he := congrArg (fun k : B ⟶ CommRingCat.of (B ⧸ J) ↦ k x) hd
    change d (j x) = q x at he
    rw [show j x = 0 from hx, map_zero] at he
    exact he.symm
  · rw [Ideal.map_le_iff_le_comap]
    intro x hx
    have he := congrArg (fun k : R ⟶ C ↦ k x) H.w
    change i (f x) = j (g x) at he
    rw [show f x = 0 from hx, map_zero] at he
    exact he.symm

variable {X Y B : Scheme} [IsAffine X] [IsAffine Y] [IsAffine B]
  (f : X ⟶ Y) (i : B ⟶ Y) [IsClosedImmersion i]

/-- The original boundary ideal extends to the exact kernel on the closed test. -/
theorem boundary_kernel_map :
    RingHom.ker (pullback.fst f i).appTop.hom =
      (RingHom.ker i.appTop.hom).map f.appTop.hom :=
  pushout_kernel (isPushout_appTop_of_isPullback (IsPullback.of_hasPullback f i)).flip
    (IsClosedImmersion.isAffine_surjective_of_isAffine i).2

variable [IsClosedImmersion f]

/-- Every restricted boundary-zero coefficient has an exact ambient boundary-zero lift. -/
theorem exists_boundary_zero_lift (z : Γ(X, ⊤))
    (hz : (pullback.fst f i).appTop z = 0) :
    ∃ a : Γ(Y, ⊤), i.appTop a = 0 ∧ f.appTop a = z := by
  have hm : z ∈ (RingHom.ker i.appTop.hom).map f.appTop.hom := by
    rw [← boundary_kernel_map f i]
    exact hz
  exact (Ideal.mem_map_iff_of_surjective f.appTop.hom
    (IsClosedImmersion.isAffine_surjective_of_isAffine f).2).mp hm

end FLT.Mazur.AffineClosedBoundaryKernelLifting
