/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.RingTheory.FiniteType

/-!
# Finite coefficient models retaining two original coefficient systems

Inside a ring of actual invariant functions, adjoin the images of both finite
coefficient rings. The resulting ring remains finite type over the integers.
No independence, injectivity, or tensor product presentation is assumed.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.FiniteCoefficientJoin
universe u v w
variable {C : Type u} {D : Type v} {B : Type w}
  [CommRing C] [CommRing D] [CommRing B] (c : C →+* B) (d : D →+* B)

/-- The actual joint coefficient subalgebra, retaining relations in the ambient ring. -/
def algebra : Subalgebra ℤ B := c.toIntAlgHom.range ⊔ d.toIntAlgHom.range

/-- The old coefficients are retained literally inside the joint model. -/
def left : C →+* algebra c d :=
  c.codRestrict _ (fun x ↦ (show c.toIntAlgHom.range ≤ algebra c d from le_sup_left) ⟨x, rfl⟩)

/-- The new coefficients are retained literally as well. -/
def right : D →+* algebra c d :=
  d.codRestrict _ (fun x ↦ (show d.toIntAlgHom.range ≤ algebra c d from le_sup_right) ⟨x, rfl⟩)

/-- The joint model still consists of the original ambient functions. -/
def inclusion : algebra c d →+* B := (algebra c d).val.toRingHom

@[simp]
theorem inclusion_left : (inclusion c d).comp (left c d) = c := rfl

@[simp]
theorem inclusion_right : (inclusion c d).comp (right c d) = d := rfl

/-- Combining two finite coefficient systems creates another finite coefficient system. -/
instance finiteType [Algebra.FiniteType ℤ C] [Algebra.FiniteType ℤ D] :
    Algebra.FiniteType ℤ (algebra c d) := by
  apply (Subalgebra.fg_iff_finiteType _).mp
  have hc : c.toIntAlgHom.range.FG := by
    simpa using (Algebra.FiniteType.out (R := ℤ) (A := C)).map c.toIntAlgHom
  have hd : d.toIntAlgHom.range.FG := by
    simpa using (Algebra.FiniteType.out (R := ℤ) (A := D)).map d.toIntAlgHom
  exact hc.sup hd

/-- The joint coefficient ring is Noetherian, even if the ambient invariant ring is not. -/
instance isNoetherianRing [Algebra.FiniteType ℤ C] [Algebra.FiniteType ℤ D] :
    IsNoetherianRing (algebra c d) := Algebra.FiniteType.isNoetherianRing ℤ _

end FLT.Mazur.FiniteCoefficientJoin
