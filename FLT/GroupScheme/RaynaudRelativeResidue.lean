/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.RaynaudUnramifiedStage

/-!
# Relative residue extensions with a fixed embedding

Lift a finite separable extension of the residue field of an existing stage.
The new stage is finite over the original base, and its closure embedding
extends the prescribed embedding of the existing stage.
-/

@[expose] public noncomputable section

universe u v w

open IsLocalRing

namespace RaynaudParameters

/-- Lift a residue extension relative to the given stage, retaining the entire
base tower and its prescribed embedding in the common algebraic closure. -/
theorem exists_relative_residue_stage
    {R : Type w} [CommRing R] {S : Type u} [CommRing S] [IsDomain S]
    [IsDiscreteValuationRing S] [Algebra R S] [Module.Finite R S]
    (Ω : Type v) [Field Ω] [IsAlgClosed Ω] [Algebra S Ω] [FaithfulSMul S Ω]
    [Algebra R Ω] [IsScalarTower R S Ω] {π : R}
    (hπ : Irreducible (algebraMap R S π))
    (k' : Type u) [Field k'] [Algebra (ResidueField S) k']
    [FiniteDimensional (ResidueField S) k'] [Algebra.IsSeparable (ResidueField S) k'] :
    ∃ (A : Type u) (_ : CommRing A) (_ : IsDomain A) (_ : IsDiscreteValuationRing A)
      (_ : Algebra S A) (_ : Module.Finite S A) (_ : IsLocalHom (algebraMap S A))
      (_ : Algebra R A) (_ : IsScalarTower R S A) (_ : Module.Finite R A)
      (_ : Algebra.FormallyUnramified S A) (f : A →ₐ[R] Ω),
      Function.Injective f ∧ (∀ s, f (algebraMap S A s) = algebraMap S Ω s) ∧
      Irreducible (algebraMap R A π) ∧
      Nonempty (ResidueField A ≃ₐ[ResidueField S] k') := by
  obtain ⟨A, hA, hdom, hdvr, hSA, hfin, hloc, f, hf, hπA, hmax, ⟨e⟩⟩ :=
    exists_embedded_unramified_stage Ω hπ k'
  let hRA : Algebra R A := ((algebraMap S A).comp (algebraMap R S)).toAlgebra
  let hRS : IsScalarTower R S A := .of_algebraMap_eq fun _ ↦ rfl
  let hFR : Module.Finite R A := Module.Finite.trans S A
  let : Algebra.IsSeparable (ResidueField S) (ResidueField A) :=
    Algebra.IsSeparable.of_algHom _ _ e.toAlgHom
  let hU : Algebra.FormallyUnramified S A :=
    Algebra.FormallyUnramified.of_map_maximalIdeal hmax.symm
  exact ⟨A, hA, hdom, hdvr, hSA, hfin, hloc, hRA, hRS, hFR, hU,
    f.restrictScalars R, hf, f.commutes, hπA, ⟨e⟩⟩

end RaynaudParameters
