/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.LiftedPresentationGeometricFibre
public import FLT.GroupScheme.NilpotentGeometricCharacteristic
public import Mathlib.RingTheory.QuasiFinite.Basic

/-! # Quasi-finiteness of the actual equations lifted across a nilpotent coefficient kernel -/

@[expose] public noncomputable section

open scoped TensorProduct

namespace Algebra.Presentation

variable {B C E ι σ : Type*} [CommRing B] [CommRing C] [CommRing E]
  [Algebra B C] [Algebra C E] [Algebra B E] [IsScalarTower B C E]
  [QuasiFinite C E]

/-- Every residue fibre of the lifted equation quotient is finite-dimensional: a field
kills the nilpotent coefficient kernel, and the specified presentation identifies the fibre. -/
theorem quasiFinite_liftedPresentation (P : Presentation C E ι σ)
    (g : σ → MvPolynomial ι B)
    (hg : ∀ i, MvPolynomial.map (algebraMap B C) (g i) = P.relation i)
    (hq : Function.Surjective (algebraMap B C)) {m : ℕ}
    (hn : RingHom.ker (algebraMap B C) ^ m = ⊥) :
    QuasiFinite B (MvPolynomial ι B ⧸ Ideal.span (Set.range g)) := by
  constructor
  intro p _
  obtain ⟨y, hy, _⟩ := RingHom.existsUnique_lift_of_nilpotent_kernel
    (algebraMap B C) hq hn (algebraMap B p.ResidueField)
  let : Algebra C p.ResidueField := y.toAlgebra
  have : IsScalarTower B C p.ResidueField :=
    IsScalarTower.of_algebraMap_eq' hy.symm
  have : Module.Finite p.ResidueField (p.ResidueField ⊗[C] E) := .of_quasiFinite
  exact Module.Finite.equiv
    (P.liftedPresentationFibreEquiv (Ω := p.ResidueField) g hg hq).symm.toLinearEquiv

end Algebra.Presentation
