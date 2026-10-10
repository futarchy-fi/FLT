/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSuccessiveXBaseChange

/-!
# Named coordinates of the actual tensor equivalence

Seal coordinate evaluation before composing the tensor equivalence with
residue normalization and ordered node splitting.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.WeierstrassSuccessiveX
variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) (s π b3 b4 b6 : R)
  (S : Type*) [CommRing S] [Algebra R S]

/-- The actual tensor equivalence retains all three original coordinates. -/
@[simp] theorem baseChangeEquiv_coord (i : Fin 3) :
    baseChangeEquiv W s π b3 b4 b6 S (tensorCoord W s π b3 b4 b6 S i) =
      extendedCoord W s π b3 b4 b6 S i := baseChangeForward_coord _ _ _ _ _ _ _ i

/-- Its inverse recovers exactly the original pure tensor of each coordinate. -/
@[simp] theorem baseChangeEquiv_symm_coord (i : Fin 3) :
    (baseChangeEquiv W s π b3 b4 b6 S).symm (extendedCoord W s π b3 b4 b6 S i) =
      tensorCoord W s π b3 b4 b6 S i := baseChangeBackward_coord _ _ _ _ _ _ _ i

end FLT.Mazur.WeierstrassSuccessiveX
