/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertIntrinsicBasisOpen
public import Mathlib.RingTheory.LocalProperties.Exactness

/-!
# Global bases detected by the intrinsic open

The intrinsic basis open is the whole spectrum exactly when the prescribed
tuple is already a global basis. No global trivialization is assumed.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.HilbertChart

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
variable [Module.FinitePresentation R M] {d : ℕ}

omit [Module.FinitePresentation R M] in
/-- A tuple is a global basis exactly when its column map is bijective. -/
theorem tuple_basis_iff_bijective (y : Fin d → M) :
    (∃ b : Module.Basis (Fin d) R M, ∀ i, b i = y i) ↔
      Function.Bijective (tupleLinearMap (R := R) y) := by
  simpa only [tupleLinearMap, Module.Basis.constr_basis] using
    exists_mapped_basis_iff (Pi.basisFun R (Fin d)) (tupleLinearMap (R := R) y)

/-- The full intrinsic open detects an actual global prescribed basis. -/
theorem intrinsicBasisOpen_eq_top_iff (y : Fin d → M) :
    intrinsicBasisOpen (R := R) y = ⊤ ↔ ∃ b : Module.Basis (Fin d) R M, ∀ i, b i = y i := by
  rw [tuple_basis_iff_bijective]
  constructor
  · intro h
    apply bijective_of_localized_maximal
    intro p hp
    have hm : (⟨p, inferInstance⟩ : PrimeSpectrum R) ∈ intrinsicBasisOpen (R := R) y := by
      rw [h]
      trivial
    exact hm
  · intro h
    apply top_unique
    intro p _
    exact ⟨LocalizedModule.map_injective _ _ h.1, LocalizedModule.map_surjective _ _ h.2⟩

end FLT.Mazur.HilbertChart
