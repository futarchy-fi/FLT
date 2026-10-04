/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.LiftedPresentationQuasiFinite
public import FLT.Mathlib.RingTheory.MvPolynomial.QuasiFiniteSquareFlat

/-! # Flatness of square presentations lifted through a nilpotent coefficient kernel -/

@[expose] public noncomputable section

namespace Algebra.Presentation

variable {B C E : Type*} [CommRing B] [CommRing C] [CommRing E]
  [Algebra B C] [Algebra C E] [Algebra B E] [IsScalarTower B C E]
  [QuasiFinite C E] {n : ℕ}

/-- The actual lifted square equations give a flat algebra over the original arbitrary
base. Only quasi-finiteness of the specified reduction and nilpotence of the kernel are used. -/
theorem flat_liftedSquarePresentation (P : Presentation C E (Fin n) (Fin n))
    (g : Fin n → MvPolynomial (Fin n) B)
    (hg : ∀ i, MvPolynomial.map (algebraMap B C) (g i) = P.relation i)
    (hq : Function.Surjective (algebraMap B C)) {m : ℕ}
    (hn : RingHom.ker (algebraMap B C) ^ m = ⊥) :
    Module.Flat B (MvPolynomial (Fin n) B ⧸ Ideal.span (Set.range g)) := by
  have := P.quasiFinite_liftedPresentation g hg hq hn
  exact MvPolynomial.flat_square_quotient_of_quasiFinite_arbitraryBase g

end Algebra.Presentation
