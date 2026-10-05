/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Deformations.HardlyRamifiedTraceParameters
public import FLT.AbsoluteGaloisGroup.HermiteFiniteRepresentations

/-!
# Finite HR trace parameters under an arithmetic discriminant bound

The fields here are cut out by the actual specialized HR trace representation.
Their degrees are bounded and arithmetic inertia away from 2p fixes them.
Hermite finiteness plus trace-map injectivity reduces finiteness of maps to a
finite test ring to a uniform discriminant bound. That bound is not asserted.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory GaloisRepresentation
namespace Deformation
open ProartinianCat MoritaReconstruction GaloisRepresentation.Extensions
variable (O : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O]
  [Finite (IsLocalRing.ResidueField O)]
  {p : ℕ} [Fact p.Prime] (hp : Odd p)
  [Algebra ℤ_[p] (residueField (𝓞 := O))] [Algebra ℤ_[p] O]
  [IsScalarTower ℤ_[p] O (residueField (𝓞 := O))]
  {V : Type} [AddCommGroup V] [Module (residueField (𝓞 := O)) V]
  [Module.Finite (residueField (𝓞 := O)) V] [Module.Free (residueField (𝓞 := O)) V]
  (hdim : Module.rank (residueField (𝓞 := O)) V = 2)
  (ρ : GaloisRep ℚ (residueField (𝓞 := O)) V) (hρ : IsHardlyRamified hp hdim ρ)
local notation "G" => Field.absoluteGaloisGroup ℚ
local notation "r" => hardlyTwoFramedResidual O hp hdim ρ hρ
local notation "H" => hardlyFlatObject O hp hdim ρ hρ
local notation "T" => hardlyTraceImageObject O hp hdim ρ hρ
local notation "inc" => hardlyTraceImageInclusion O hp hdim ρ hρ

variable (hirr : ρ.IsIrreducible)

variable (A : ProartinianCat O) [Finite A] [DiscreteTopology A]

/-- The exact kernel field of a specialization of the HR trace lift. -/
def hardlyTraceParameterField (f : T ⟶ A) :
    FiniteGaloisIntermediateField ℚ (AlgebraicClosure ℚ) :=
  finiteImageField (hardlyTraceParameterRepresentation O hp hdim ρ hρ hirr A f)

/-- Its degree is bounded uniformly in the coefficient map to the fixed test ring. -/
theorem hardlyTraceParameterField_degree_le (f : T ⟶ A) :
    Module.finrank ℚ (hardlyTraceParameterField O hp hdim ρ hρ hirr A f) ≤
      Nat.card (GL (Fin 2) A) :=
  finiteImageField_finrank_le (hardlyTraceParameterRepresentation O hp hdim ρ hρ hirr A f)

omit [Finite A] in
/-- All the specified arithmetic inertia elements fix this same field pointwise. -/
theorem hardlyTraceParameterField_inertia (f : T ⟶ A) (g : G)
    (hg : g ∈ hardlyAwayInertia p) :
    g ∈ (hardlyTraceParameterField O hp hdim ρ hρ hirr A f).toIntermediateField.fixingSubgroup := by
  change g ∈ (finiteImageField
    (hardlyTraceParameterRepresentation O hp hdim ρ hρ hirr A f)).toIntermediateField.fixingSubgroup
  rw [finiteImageField_fixingSubgroup]
  exact hardlyTraceParameterRepresentation_inertia O hp hdim ρ hρ hirr A f g hg

/-- Only finitely many image-ring maps have kernel field discriminant bounded by B. -/
theorem finite_hardlyTraceParameters_discr_bdd (B : ℕ) :
    {f : T ⟶ A | |NumberField.discr
      (hardlyTraceParameterField O hp hdim ρ hρ hirr A f)| ≤ B}.Finite :=
  (finite_representations_discr_bdd B).preimage
    (f := hardlyTraceParameterRepresentation O hp hdim ρ hρ hirr A)
    (hardlyTraceParameterRepresentation_injective O hp hdim ρ hρ hirr A).injOn

/-- The exact remaining discriminant input suffices for finiteness at each finite
coefficient test ring. No arithmetic bound or Noetherianity is assumed as a field. -/
theorem finite_hardlyTraceParameters_of_discr_bound (B : ℕ)
    (hB : ∀ f : T ⟶ A, |NumberField.discr
      (hardlyTraceParameterField O hp hdim ρ hρ hirr A f)| ≤ B) : Finite (T ⟶ A) := by
  apply Set.finite_univ_iff.mp
  exact (finite_hardlyTraceParameters_discr_bdd O hp hdim ρ hρ hirr A B).subset
    (fun f _ ↦ hB f)

end Deformation
