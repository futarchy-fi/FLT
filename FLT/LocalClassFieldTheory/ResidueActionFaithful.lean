/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.ResidueAction
public import FLT.Mathlib.RingTheory.DiscreteValuationRing.ResidueGenerator
public import FLT.Mathlib.RingTheory.Unramified.PowerBasis

/-!
# Faithful residue action of an unramified DVR algebra

An integral power basis is constructed from the separable residue extension.
The unit derivative makes its generator rigid under reduction.
-/

@[expose] public noncomputable section

namespace LocalClassFieldTheory

open IsLocalRing

variable (R S : Type*) [CommRing R] [IsLocalRing R] [CommRing S]
  [IsDomain S] [IsDiscreteValuationRing S] [Algebra R S]
  [Module.Finite R S] [Module.Free R S] [IsLocalHom (algebraMap R S)]
  [Algebra.IsSeparable (ResidueField R) (ResidueField S)]
  [Algebra.FormallyUnramified R S]

/-- Reduction is faithful on automorphisms of a finite free unramified DVR
algebra. The power basis needed in the proof is constructed, not supplied. -/
theorem residueAction_injective : Function.Injective (residueAction R S) := by
  obtain ⟨pb⟩ := nonempty_powerBasis_of_separable_residue (R := R) (S := S)
  intro σ τ h
  have heq : σ.toAlgHom = τ.toAlgHom := pb.algHomEqOfResidueEq _ _
    (congrArg (fun e => e (residue S pb.gen)) h)
  exact AlgEquiv.ext fun x => DFunLike.congr_fun heq x

/-- Unramifiedness forces the actual ideal inertia subgroup to be trivial. -/
theorem residueInertia_eq_bot : (maximalIdeal S).inertia (S ≃ₐ[R] S) = ⊥ := by
  rw [← residueAction_ker]
  exact (MonoidHom.ker_eq_bot_iff _).mpr (residueAction_injective R S)

end LocalClassFieldTheory
