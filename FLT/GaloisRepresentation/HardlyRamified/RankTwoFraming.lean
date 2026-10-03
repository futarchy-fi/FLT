/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Deformations.RepresentationTheory.GaloisRep

/-! # Framing a rank-two scalar extension without changing its representation -/

@[expose] public noncomputable section
open scoped TensorProduct
namespace GaloisRepresentation
variable {R V : Type*} [CommRing R] [Nontrivial R] [AddCommGroup V] [Module R V]
  [Module.Free R V] [Module.Finite R V]
  (A : Type*) [Field A] [Algebra R A]

/-- A chosen basis of the actual extended module gives a rank-two framing. -/
def rankTwoFrame (hV : Module.rank R V = 2) : A ⊗[R] V ≃ₗ[A] (Fin 2 → A) :=
  (Module.finBasisOfFinrankEq A (A ⊗[R] V)
    (Module.finrank_eq_of_rank_eq (by simpa [Module.rank_baseChange] using hV))).equivFun

end GaloisRepresentation
