/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineClosedBoundaryKernelLifting

/-!
# Simultaneous sections on two full affine closed subschemes

Two sections agreeing on their scheme-theoretic intersection have one ambient
lift. The exact ring pushout retains all nilpotent equations.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.AffineClosedSimultaneousLifting
set_option backward.isDefEq.respectTransparency false
variable {X Y B Z : Scheme.{0}} [IsAffine X] [IsAffine Y] [IsAffine B]
  (f : X ⟶ Y) (i : B ⟶ Y) (j : Z ⟶ X) (g : Z ⟶ B)
  (H : IsPullback j g f i) [IsClosedImmersion f] [IsClosedImmersion i]

include H in
/-- Exact intersection compatibility is sufficient for simultaneous ambient lifting. -/
theorem exists_lift (x : Γ(X, ⊤)) (y : Γ(B, ⊤))
    (hxy : j.appTop x = g.appTop y) :
    ∃ a : Γ(Y, ⊤), f.appTop a = x ∧ i.appTop a = y := by
  obtain ⟨b, hb⟩ := (IsClosedImmersion.isAffine_surjective_of_isAffine i).2 y
  have hk : RingHom.ker j.appTop.hom =
      (RingHom.ker i.appTop.hom).map f.appTop.hom :=
    AffineClosedBoundaryKernelLifting.pushout_kernel
      (isPushout_appTop_of_isPullback H).flip
      (IsClosedImmersion.isAffine_surjective_of_isAffine i).2
  have hz : x - f.appTop b ∈ (RingHom.ker i.appTop.hom).map f.appTop.hom := by
    rw [← hk]
    change j.appTop (x - f.appTop b) = 0
    rw [map_sub, hxy]
    have he := congrArg (fun k : Z ⟶ Y ↦ k.appTop b) H.w
    change j.appTop (f.appTop b) = g.appTop (i.appTop b) at he
    rw [he, hb, sub_self]
  obtain ⟨c, hc, hcx⟩ := (Ideal.mem_map_iff_of_surjective f.appTop.hom
    (IsClosedImmersion.isAffine_surjective_of_isAffine f).2).mp hz
  refine ⟨c + b, ?_, ?_⟩
  · rw [map_add, hcx, sub_add_cancel]
  · rw [map_add, show i.appTop c = 0 from hc, zero_add, hb]

end FLT.Mazur.AffineClosedSimultaneousLifting
