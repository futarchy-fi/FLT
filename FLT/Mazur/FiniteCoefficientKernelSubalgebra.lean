/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteCoefficientDifferenceIdeal
public import Mathlib.RingTheory.FiniteType

/-!
# A finite type coefficient subalgebra preserving the full equality kernel

Adjoin the finitely many actual coefficient equations to the original base.
The resulting subalgebra is finite type, and is Noetherian over a Noetherian
base. Restricting the two coefficient maps to it leaves every equality test
unchanged. The full coefficient ring itself need not be Noetherian.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.FiniteCoefficientDifference
universe u v w z
variable (R : Type u) {B : Type v} {T : Type w}
  [CommRing R] [CommRing B] [CommRing T] [Algebra R B]
  (l r : B →+* T) [IsNoetherianRing T]

/-- The finite type subalgebra of actual coefficients, over the unchanged base. -/
def kernelSubalgebra : Subalgebra R B :=
  Algebra.adjoin R (coefficients l r : Set B)

/-- Each original selected coefficient lies in the constructed subalgebra. -/
theorem coefficient_mem_kernelSubalgebra (b : B) (hb : b ∈ coefficients l r) :
    b ∈ kernelSubalgebra R l r := Algebra.subset_adjoin hb

/-- The construction is finite type over the original base ring. -/
instance kernelSubalgebra_finiteType : Algebra.FiniteType R (kernelSubalgebra R l r) := by
  unfold kernelSubalgebra
  exact Algebra.FiniteType.adjoin_of_finite (Finset.finite_toSet _)

/-- The constructed coefficient ring is Noetherian when the unchanged base is Noetherian. -/
instance kernelSubalgebra_isNoetherianRing [IsNoetherianRing R] :
    IsNoetherianRing (kernelSubalgebra R l r) :=
  Algebra.FiniteType.isNoetherianRing R _

/-- Restriction to the finite type coefficient subalgebra preserves all ring-valued kernel tests. -/
theorem equalizes_iff_kernelSubalgebra {C : Type z} [CommRing C] (g : T →+* C) :
    g.comp l = g.comp r ↔
      (g.comp l).comp (kernelSubalgebra R l r).val.toRingHom =
        (g.comp r).comp (kernelSubalgebra R l r).val.toRingHom := by
  constructor
  · intro h
    rw [h]
  · intro h
    apply (equalizes_iff_coefficients l r g).mpr
    intro b hb
    exact DFunLike.congr_fun h ⟨b, coefficient_mem_kernelSubalgebra R l r b hb⟩

/-- Passing to the finite type subalgebra retains the full ideal, including nilpotent equations. -/
theorem kernelSubalgebra_differenceIdeal :
    differenceIdeal (l.comp (kernelSubalgebra R l r).val.toRingHom)
      (r.comp (kernelSubalgebra R l r).val.toRingHom) = differenceIdeal l r := by
  apply le_antisymm
  · rw [differenceIdeal, Ideal.span_le]
    rintro _ ⟨b, rfl⟩
    exact Ideal.subset_span ⟨b.val, rfl⟩
  · rw [differenceIdeal_eq l r, Ideal.span_le]
    rintro _ ⟨b, hb, rfl⟩
    exact Ideal.subset_span
      ⟨⟨b, coefficient_mem_kernelSubalgebra R l r b hb⟩, rfl⟩

end FLT.Mazur.FiniteCoefficientDifference
