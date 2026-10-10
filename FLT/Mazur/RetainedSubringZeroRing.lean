/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RetainedSubringGrading

/-!
# Retaining degrees keeps the original degree-zero ring

Inclusion of the retained subring identifies its internal degree-zero ring
with the original internal degree-zero ring, preserving its original elements.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.RetainedSubringZeroRing

open RetainedSubringGrading

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {A σ : Type*} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  (𝒜 : ℕ → σ) [GradedRing 𝒜] (q : ℕ)

/-- Inclusion identifies the two original degree-zero rings. -/
def ringEquiv : grade 𝒜 q 0 ≃+* 𝒜 0 where
  toFun s := ⟨s.val.val, by
    have hs : s.val.val ∈ 𝒜 (q * 0) := s.property
    simpa only [Nat.mul_zero] using hs⟩
  invFun s := by
    have hs : s.val ∈ 𝒜 (q * 0) := by simpa only [Nat.mul_zero] using s.property
    exact ⟨⟨s.val, Subring.subset_closure (Set.mem_iUnion.mpr ⟨0, hs⟩)⟩, hs⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl

/-- The zero-degree comparison is the original subring inclusion. -/
theorem ringEquiv_val (s : grade 𝒜 q 0) : (ringEquiv 𝒜 q s).val = s.val.val := rfl

/-- Its inverse retains the original degree-zero element as an actual retained section. -/
theorem ringEquiv_symm_val (s : 𝒜 0) : ((ringEquiv 𝒜 q).symm s).val.val = s.val := rfl

end FLT.Mazur.RetainedSubringZeroRing
