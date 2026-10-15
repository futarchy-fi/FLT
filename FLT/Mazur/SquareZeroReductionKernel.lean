/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Nilpotent.Lemmas

/-!
# Square-zero kernels over reduced rings

A square-zero kernel mapping onto a reduced ring is the entire nilradical.
Quotienting by a smaller ideal is reduced exactly when that ideal already
contains the kernel. This distinguishes a reduced quotient from merely
having the expected reduction.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.SquareZeroReductionKernel
variable {A N : Type*} [CommRing A] [CommRing N] [IsReduced N]
  (r : A →+* N) (hsq : ∀ z, r z = 0 → z * z = 0)

include hsq in
/-- A square-zero kernel with reduced target is exactly the full nilradical. -/
theorem ker_eq_nilradical : RingHom.ker r = nilradical A := by
  ext z
  constructor
  · intro hz
    exact ⟨2, (pow_two z).trans (hsq z hz)⟩
  · intro hz
    exact (show IsNilpotent z from hz).map r |>.eq_zero

/-- The quotient by this concrete kernel recovers the given reduced target. -/
def reducedEquiv (hr : Function.Surjective r) : A ⧸ nilradical A ≃+* N :=
  (Ideal.quotEquivOfEq (ker_eq_nilradical r hsq).symm).trans
    (r.quotientKerEquivOfSurjective hr)

omit [IsReduced N] in
include hsq in
/-- Reducedness of an intermediate quotient kills every remaining kernel element. -/
theorem ker_le_of_quotient_reduced (I : Ideal A) [IsReduced (A ⧸ I)] : RingHom.ker r ≤ I := by
  intro z hz
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  have hn : IsNilpotent z := ⟨2, (pow_two z).trans (hsq z hz)⟩
  exact (hn.map (Ideal.Quotient.mk I)).eq_zero

include hsq in
/-- A quotient by an ideal inside the kernel is reduced precisely when no kernel remains. -/
theorem quotient_reduced_iff (I : Ideal A) (hI : I ≤ RingHom.ker r) :
    IsReduced (A ⧸ I) ↔ RingHom.ker r ≤ I := by
  constructor
  · intro hi
    let _ := hi
    exact ker_le_of_quotient_reduced r hsq I
  · intro hi
    exact isReduced_of_injective (Ideal.Quotient.lift I r hI)
      ((Ideal.injective_lift_iff _).mpr (le_antisymm hi hI))

end FLT.Mazur.SquareZeroReductionKernel
