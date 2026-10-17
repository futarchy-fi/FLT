/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.BoundaryCorrectionBoundaryImage

/-!
# The kernel of the original boundary obstruction map

A boundary class vanishes exactly when it has a single family of original
chart lifts satisfying every full mixed equation. The extended boundary map
also vanishes on scalar extensions of every such original solution.
-/

@[expose] public noncomputable section
open TensorProduct
namespace FLT.Mazur.BoundaryCorrectionIdeal
variable {R : Type*} [CommRing R] {ι : Type*} {A B : ι → Type*} {C : ι → ι → Type*}
  [∀ i, CommRing (A i)] [∀ i, CommRing (B i)] [∀ i j, CommRing (C i j)]
  [∀ i, Algebra R (A i)] [∀ i, Algebra R (B i)] [∀ i j, Algebra R (C i j)]
  (φ : ∀ i, A i →ₐ[R] B i)
  (p : ∀ i j, A i →ₐ[R] C i j) (q : ∀ i j, A j →ₐ[R] C i j)
  (v : ∀ i, A i) {D : Type*} [AddCommGroup D] [Module R D]
  (β : D →ₗ[R] (∀ i, B i))
set_option quotPrecheck false
local notation "F" => originalCorrectionOperator φ p q v

/-- The obstruction map before scalar extension, with the full original correction cokernel. -/
def originalBoundaryCokernelMap : D →ₗ[R]
    (((∀ i, B i) × ∀ i j, C i j) ⧸ LinearMap.range F) :=
  (LinearMap.range F).mkQ.comp ((LinearMap.inl R (∀ i, B i) (∀ i j, C i j)).comp β)

/-- Vanishing means exact simultaneous original lifts, with no residual equations omitted. -/
theorem originalBoundaryCokernelMap_eq_zero_iff (t : D) :
    originalBoundaryCokernelMap φ p q v β t = 0 ↔
      ∃ w : ∀ i, A i, (∀ i, φ i (w i) = β t i) ∧
        ∀ i j, p i j (w i) = q i j (w j) := by
  change (LinearMap.range F).mkQ (β t, 0) = 0 ↔ _
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  constructor
  · rintro ⟨w, hw⟩
    rw [originalCorrectionOperator_apply] at hw
    exact ⟨w, congrFun (congrArg Prod.fst hw), fun i j ↦
      sub_eq_zero.mp (congrFun (congrFun (congrArg Prod.snd hw) i) j)⟩
  · rintro ⟨w, hb, hm⟩
    refine ⟨w, ?_⟩
    rw [originalCorrectionOperator_apply]
    exact Prod.ext (funext hb) (by funext i j; exact sub_eq_zero.mpr (hm i j))

variable (S : Type*) [CommRing S] [Algebra R S]

/-- Every original solution remains zero in the full extended boundary cokernel. -/
theorem boundaryCokernelMap_tmul_eq_zero (t : D)
    (ht : originalBoundaryCokernelMap φ p q v β t = 0) (s : S) :
    boundaryCokernelMap φ p q v β S (s ⊗ₜ[R] t) = 0 := by
  obtain ⟨w, hb, hm⟩ := (originalBoundaryCokernelMap_eq_zero_iff φ p q v β t).mp ht
  rw [boundaryCokernelMap_tmul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  refine ⟨s ⊗ₜ[R] w, ?_⟩
  rw [ambientCorrectionOperator_eq_baseChange, LinearMap.baseChange_tmul,
    originalCorrectionOperator_apply]
  have hw : (fun i ↦ φ i (w i), fun i j ↦ p i j (w i) - q i j (w j)) = (β t, 0) :=
    Prod.ext (funext hb) (by funext i j; exact sub_eq_zero.mpr (hm i j))
  rw [hw]

end FLT.Mazur.BoundaryCorrectionIdeal
