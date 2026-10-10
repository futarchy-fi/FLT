/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.RingTheory.LocalRing.Module

/-!
# Detecting finite-module vanishing on residue fibers

For a finite module, vanishing after tensoring with every prime residue field
forces the module itself to vanish. This is the Nakayama input for descending
from fiberwise cohomology vanishing in a bounded flat complex.
-/

@[expose] public noncomputable section
open TensorProduct
namespace FLT.Mazur.FiniteModuleFiberVanishing

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] [Module.Finite R M]

/-- A finite module vanishes when all its actual residue-field fibers vanish. -/
theorem subsingleton_of_residue_fields
    (h : ∀ p : PrimeSpectrum R, Subsingleton (p.asIdeal.ResidueField ⊗[R] M)) :
    Subsingleton M := by
  apply (Module.support_eq_empty_iff (R := R)).mp
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro p hp
  let _ := h p
  have hn := (Module.mem_support_iff_nontrivial_residueField_tensorProduct p).mp hp
  exact not_nontrivial (p.asIdeal.ResidueField ⊗[R] M) hn

end FLT.Mazur.FiniteModuleFiberVanishing
