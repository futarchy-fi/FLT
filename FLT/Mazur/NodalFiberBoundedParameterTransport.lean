/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.NodalFiberParameterTransport

/-!
# Sealed transport for evaluation of residue comparisons

Retain the exact constant and Laurent equivalences while bounding reduction
of their dependent coefficient casts in composite tensor comparisons.
-/

@[expose] public noncomputable section
open LaurentPolynomial
open scoped LaurentPolynomial
namespace FLT.Mazur.NodalFiber
variable {R : Type*} [CommRing R]

/-- Package the constructed transport together with its equality proof. -/
opaque constantTransportSeal (c d : R) (h : c = d) :
    {e : Coordinate c ≃ₐ[R] Coordinate d // e = constantEquiv c d h} :=
  ⟨constantEquiv c d h, rfl⟩

/-- Seal the actual constant transport. -/
def constantBoundedEquiv (c d : R) (h : c = d) :
    Coordinate c ≃ₐ[R] Coordinate d := (constantTransportSeal c d h).val

/-- The sealed map is exactly the original transport. -/
theorem constantBoundedEquiv_def (c d : R) (h : c = d) :
    constantBoundedEquiv c d h = constantEquiv c d h :=
  (constantTransportSeal c d h).property

/-- Sealing preserves the first tangent coordinate. -/
theorem constantBoundedEquiv_p (c d : R) (h : c = d) :
    constantBoundedEquiv c d h (p c) = p d := by
  rw [constantBoundedEquiv_def, constantEquiv_p]

/-- Sealing preserves the second tangent coordinate. -/
theorem constantBoundedEquiv_q (c d : R) (h : c = d) :
    constantBoundedEquiv c d h (q c) = q d := by
  rw [constantBoundedEquiv_def, constantEquiv_q]

/-- Package the constructed Laurent comparison and its equality proof. -/
opaque unitLaurentTransportSeal (u : Rˣ) (c : R) (h : ↑u = c) :
    {e : Coordinate c ≃ₐ[R] R[T;T⁻¹] // e = unitLaurentCast u c h} :=
  ⟨unitLaurentCast u c h, rfl⟩

/-- Seal the actual transported Laurent comparison. -/
def unitLaurentBoundedCast (u : Rˣ) (c : R) (h : ↑u = c) :
    Coordinate c ≃ₐ[R] R[T;T⁻¹] := (unitLaurentTransportSeal u c h).val

/-- The sealed comparison is exactly the transported Laurent comparison. -/
theorem unitLaurentBoundedCast_def (u : Rˣ) (c : R) (h : ↑u = c) :
    unitLaurentBoundedCast u c h = unitLaurentCast u c h :=
  (unitLaurentTransportSeal u c h).property

/-- The first tangent factor retains its Laurent coordinate. -/
theorem unitLaurentBoundedCast_p (u : Rˣ) (c : R) (h : ↑u = c) :
    unitLaurentBoundedCast u c h (p c) = T 1 := by
  rw [unitLaurentBoundedCast_def, unitLaurentCast_p]

/-- The second tangent factor retains the actual constant coefficient. -/
theorem unitLaurentBoundedCast_q (u : Rˣ) (c : R) (h : ↑u = c) :
    unitLaurentBoundedCast u c h (q c) = C c * T (-1) := by
  rw [unitLaurentBoundedCast_def, unitLaurentCast_q]

end FLT.Mazur.NodalFiber
