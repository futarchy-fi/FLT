/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Deformations.RepresentationTheory.ULiftCoefficientTensor
public import FLT.GaloisRepresentation.HardlyRamified.BaseChangeUniverses
public import FLT.GaloisRepresentation.HardlyRamified.CoordinateChange
public import FLT.GaloisRepresentation.HardlyRamified.FlatCoefficientQuotientUniverses

/-! # Hardly ramified models in independently lifted universes -/

@[expose] public noncomputable section
attribute [local instance 2000] TensorProduct.leftModule
open scoped TensorProduct
universe u v
namespace GaloisRepresentation
variable {p : ℕ} [Fact p.Prime] {R V : Type*}
  [CommRing R] [IsLocalRing R] [TopologicalSpace R] [IsTopologicalRing R]
  [Algebra ℤ_[p] R] [AddCommGroup V] [Module R V] [Module.Finite R V] [Module.Free R V]

/-- Freeness is preserved under independent lifts of scalars and vectors. -/
instance uliftCoefficientsFree : Module.Free (ULift.{u} R) (ULift.{v} V) :=
  Module.Free.of_equiv (uliftCoefficientTensor (R := R) (V := V))

/-- Finiteness is preserved under independent lifts of scalars and vectors. -/
instance uliftCoefficientsFinite : Module.Finite (ULift.{u} R) (ULift.{v} V) :=
  Module.Finite.equiv (uliftCoefficientTensor (R := R) (V := V))

omit [TopologicalSpace R] [IsTopologicalRing R] in
/-- The independently lifted lattice retains rank two. -/
theorem uliftCoefficients_rank (hV : Module.rank R V = 2) :
    Module.rank (ULift.{u} R) (ULift.{v} V) = 2 := by
  rw [← Module.finrank_eq_rank]
  have h : Module.rank (ULift.{u} R) (ULift.{u} R ⊗[R] V) = 2 := by
    simpa [Module.rank_baseChange] using hV
  rw [← (uliftCoefficientTensor (R := R) (V := V)).finrank_eq,
    Module.finrank_eq_of_rank_eq h]
  rfl

/-- The lifted coefficient ring inherits localness from the original one. -/
instance uliftCoefficientsLocal : IsLocalRing (ULift.{u} R) :=
  (ULift.ringEquiv : ULift.{u} R ≃+* R).symm.isLocalRing

/-- The original coefficient ring acts continuously on its lifted copy. -/
instance uliftCoefficientsContinuousSMul : ContinuousSMul R (ULift.{u} R) :=
  continuousSMul_of_algebraMap R _ continuous_uliftUp

/-- Scalar extension and the actual tensor comparison give the lifted representation. -/
def uliftCoefficients (ρ : GaloisRep ℚ R V) :
    GaloisRep ℚ (ULift.{u} R) (ULift.{v} V) :=
  (ρ.baseChange (ULift.{u} R)).conj uliftCoefficientTensor

/-- All hardly ramified clauses survive the independent universe lifts. -/
theorem IsHardlyRamified.uliftCoefficients (hp : Odd p) (hV : Module.rank R V = 2)
    {ρ : GaloisRep ℚ R V} (hρ : IsHardlyRamified hp hV ρ) :
    IsHardlyRamified hp (uliftCoefficients_rank.{u, v} hV) (uliftCoefficients ρ) := by
  have hVS : Module.rank (ULift.{u} R) (ULift.{u} R ⊗[R] V) = 2 := by
    simpa [Module.rank_baseChange] using hV
  have hsurj : Function.Surjective (algebraMap R (ULift.{u} R)) := fun x ↦ ⟨x.down, rfl⟩
  have hflat := ThreeAdicPlan.flatAt_quotient_universes hsurj ρ _ hρ.isFlat
  exact (ThreeAdicPlan.hardlyRamified_baseChange_of_flat_universes hp hV hVS hρ hflat).conj
    hp hVS (uliftCoefficients_rank hV) uliftCoefficientTensor

end GaloisRepresentation
