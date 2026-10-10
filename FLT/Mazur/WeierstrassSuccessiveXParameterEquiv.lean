/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSuccessiveXAlgebra

/-!
# Parameter normalization of the actual three-coordinate equation

Equal parameters induce a coefficient algebra equivalence that fixes every
named generator. This seals dependent transports needed for residue fibers.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.WeierstrassSuccessiveX
variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)
  (s π b3 b4 b6 t ρ c3 c4 c6 : R)
  (hs : s = t) (hπ : π = ρ) (h3 : b3 = c3) (h4 : b4 = c4) (h6 : b6 = c6)

/-- Normalize equal parameters without discarding any of the three actual coordinates. -/
def parameterEquiv : Coordinate W s π b3 b4 b6 ≃ₐ[R] Coordinate W t ρ c3 c4 c6 := by
  subst t ρ c3 c4 c6
  exact AlgEquiv.refl

/-- Parameter normalization fixes each original named generator. -/
@[simp] theorem parameterEquiv_coord (i : Fin 3) :
    parameterEquiv W s π b3 b4 b6 t ρ c3 c4 c6 hs hπ h3 h4 h6
      (coord W s π b3 b4 b6 i) = coord W t ρ c3 c4 c6 i := by
  subst t ρ c3 c4 c6
  rfl

end FLT.Mazur.WeierstrassSuccessiveX
