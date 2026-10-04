/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Deformations.HardlyRamifiedFlatLift
public import FLT.AbsoluteGaloisGroup.HermiteFiniteRepresentations

/-!
# Finite test-ring parameters of the framed HR quotient

Specialization of the constructed framed lift is injective on parameter maps.
Its actual kernel field has uniformly bounded degree and is fixed by the
specified inertia away from 2p. A uniform discriminant bound would therefore
make the finite-test-ring parameter set finite; the bound remains arithmetic work.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory GaloisRepresentation
namespace Deformation
open ProartinianCat GaloisRepresentation.Extensions
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
local notation "H" => hardlyFlatObject O hp hdim ρ hρ

/-- Specialization of the same universal framed HR representation. -/
def hardlyFramedParameterRepresentation (A : ProartinianCat O) (f : H ⟶ A) :
    G →ₜ* GL (Fin 2) A :=
  (repnFunctor (Fin 2) G O).map f (hardlyFlatLift O hp hdim ρ hρ).val

/-- The actual framed representation determines its coefficient parameter. -/
theorem hardlyFramedParameterRepresentation_injective (A : ProartinianCat O) :
    Function.Injective (hardlyFramedParameterRepresentation O hp hdim ρ hρ A) := by
  intro f h he
  have he' : hardlyFlatProjection O hp hdim ρ hρ ≫ f =
      hardlyFlatProjection O hp hdim ρ hρ ≫ h := by
    apply (hardlyArithmeticEquiv O hp hdim ρ hρ A).injective
    apply Subtype.ext
    apply Subtype.ext
    exact he
  apply ProartinianCat.hom_ext
  ext x
  obtain ⟨y, rfl⟩ := hardlyFlatProjection_surjective O hp hdim ρ hρ x
  exact congrArg (fun k ↦ ProartinianCat.Hom.hom k y) he'

/-- Arithmetic inertia remains trivial in every specialization. -/
theorem hardlyFramedParameterRepresentation_inertia (A : ProartinianCat O) (f : H ⟶ A)
    (g : G) (hg : g ∈ hardlyAwayInertia p) :
    hardlyFramedParameterRepresentation O hp hdim ρ hρ A f g = 1 := by
  have hi := (trivial_hardlyAwayInertia_iff p
    (FramedGaloisRep.ofGL (hardlyFlatLift O hp hdim ρ hρ).val)).mpr
    (hardlyFlatLift_unramified O hp hdim ρ hρ) g hg
  have hi' : (hardlyFlatLift O hp hdim ρ hρ).val g = 1 := by
    simpa only [FramedGaloisRep.ofGL, Equiv.apply_symm_apply] using hi
  change Matrix.GeneralLinearGroup.map f.hom.toRingHom
    ((hardlyFlatLift O hp hdim ρ hρ).val g) = 1
  rw [hi', map_one]

variable (A : ProartinianCat O) [Finite A] [DiscreteTopology A]

/-- The finite Galois field cut out by a framed HR specialization. -/
def hardlyFramedParameterField (f : H ⟶ A) :
    FiniteGaloisIntermediateField ℚ (AlgebraicClosure ℚ) :=
  finiteImageField (hardlyFramedParameterRepresentation O hp hdim ρ hρ A f)

/-- Its degree is bounded by the order of the same fixed matrix group. -/
theorem hardlyFramedParameterField_degree_le (f : H ⟶ A) :
    Module.finrank ℚ (hardlyFramedParameterField O hp hdim ρ hρ A f) ≤
      Nat.card (GL (Fin 2) A) :=
  finiteImageField_finrank_le (hardlyFramedParameterRepresentation O hp hdim ρ hρ A f)

omit [Finite A] in
/-- The arithmetic inertia set fixes the actual finite kernel field. -/
theorem hardlyFramedParameterField_inertia (f : H ⟶ A) (g : G)
    (hg : g ∈ hardlyAwayInertia p) :
    g ∈ (hardlyFramedParameterField O hp hdim ρ hρ A f).toIntermediateField.fixingSubgroup := by
  change g ∈ (finiteImageField
    (hardlyFramedParameterRepresentation O hp hdim ρ hρ A f)).toIntermediateField.fixingSubgroup
  rw [finiteImageField_fixingSubgroup]
  exact hardlyFramedParameterRepresentation_inertia O hp hdim ρ hρ A f g hg

/-- Hermite finiteness applies to coefficient maps, not just isomorphism classes of fields. -/
theorem finite_hardlyFramedParameters_discr_bdd (B : ℕ) :
    {f : H ⟶ A | |NumberField.discr
      (hardlyFramedParameterField O hp hdim ρ hρ A f)| ≤ B}.Finite :=
  (finite_representations_discr_bdd B).preimage
    (f := hardlyFramedParameterRepresentation O hp hdim ρ hρ A)
    (hardlyFramedParameterRepresentation_injective O hp hdim ρ hρ A).injOn

/-- A uniform kernel-field discriminant bound gives finite framed parameters
at the chosen finite test ring. No such arithmetic bound is assumed implicitly. -/
theorem finite_hardlyFramedParameters_of_discr_bound (B : ℕ)
    (hB : ∀ f : H ⟶ A, |NumberField.discr
      (hardlyFramedParameterField O hp hdim ρ hρ A f)| ≤ B) : Finite (H ⟶ A) := by
  apply Set.finite_univ_iff.mp
  exact (finite_hardlyFramedParameters_discr_bdd O hp hdim ρ hρ A B).subset
    (fun f _ ↦ hB f)

end Deformation
