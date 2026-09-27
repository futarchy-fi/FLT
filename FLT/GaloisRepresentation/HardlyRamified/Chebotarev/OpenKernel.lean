/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import Mathlib.FieldTheory.AbsoluteGaloisGroup

/-!
# Open kernels of finite Galois quotients

This proves leaf G1 of `docs/CHEBOTAREV_PLAN.md`: the kernel of a continuous
homomorphism to a finite discrete group is open. Finiteness is retained in the
interface for finite quotients, although discreteness alone suffices.
-/

@[expose] public section

namespace GaloisRepresentation.Chebotarev

/-- A continuous finite discrete quotient of the absolute Galois group of `ℚ`
has open kernel. -/
@[nolint unusedArguments]
theorem isOpen_ker {G : Type*} [Group G] [Finite G]
    [TopologicalSpace G] [DiscreteTopology G]
    (f : Field.absoluteGaloisGroup ℚ →ₜ* G) :
    IsOpen (f.toMonoidHom.ker : Set (Field.absoluteGaloisGroup ℚ)) := by
  exact (isOpen_discrete ({1} : Set G)).preimage f.continuous

end GaloisRepresentation.Chebotarev
