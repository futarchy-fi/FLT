/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree

/-!
# The affine action associated to a cocycle

A crossed homomorphism gives an action on the underlying coefficient set.
Its kernel simultaneously kills the cocycle and the coefficient action.
-/

@[expose] public section

namespace GaloisRepresentation.Extensions

variable {G M : Type*} [Group G] [AddCommGroup M] [DistribMulAction G M]

/-- The permutation associated to a cocycle and a group element. -/
def cocyclePerm (c : G → M) (g : G) :
    Equiv.Perm M where
  toFun x := g • x + c g
  invFun x := g⁻¹ • (x - c g)
  left_inv x := by simp
  right_inv x := by simp

/-- A cocycle acts by affine permutations. -/
def cocycleAction (c : G → M) (hc : groupCohomology.IsCocycle₁ c) :
    G →* Equiv.Perm M where
  toFun := cocyclePerm c
  map_one' := by
    ext x
    simp [cocyclePerm, groupCohomology.map_one_of_isCocycle₁ hc]
  map_mul' g h := by
    ext x
    simp [cocyclePerm, hc g h, smul_add, mul_smul, add_assoc]

/-- The affine action remembers the cocycle by evaluation at zero. -/
@[simp] theorem cocycleAction_apply_zero (c : G → M)
    (hc : groupCohomology.IsCocycle₁ c) (g : G) :
    cocycleAction c hc g 0 = c g := by
  simp [cocycleAction, cocyclePerm]

/-- An element is in the affine kernel exactly when it kills the cocycle
and acts trivially on all coefficients. -/
theorem mem_cocycleAction_ker (c : G → M) (hc : groupCohomology.IsCocycle₁ c)
    (g : G) : g ∈ (cocycleAction c hc).ker ↔ c g = 0 ∧ ∀ x : M, g • x = x := by
  change cocycleAction c hc g = 1 ↔ _
  constructor
  · intro h
    have hz : c g = 0 := by
      simpa using congrArg (fun e : Equiv.Perm M ↦ e 0) h
    refine ⟨hz, fun x ↦ ?_⟩
    simpa [cocycleAction, cocyclePerm, hz] using
      congrArg (fun e : Equiv.Perm M ↦ e x) h
  · rintro ⟨hz, hx⟩
    ext x
    simp [cocycleAction, cocyclePerm, hz, hx]

end GaloisRepresentation.Extensions
