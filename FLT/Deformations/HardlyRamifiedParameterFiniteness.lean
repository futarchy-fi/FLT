/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Deformations.HardlyRamifiedParameterBounds
public import FLT.NumberField.UniformDifferentExponent

/-!
# Unconditional finiteness of HR coefficient parameters

The degree bound controls the different at 2 and p in the actual parameter
fields. Together with unramifiedness elsewhere, this proves the explicit
Hermite discriminant bound and finiteness for every finite test ring.
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

local notation "T" => hardlyTraceImageObject O hp hdim ρ hρ

variable (hirr : ρ.IsIrreducible)
variable (A : ProartinianCat O) [Finite A] [DiscreteTopology A]

/-- The actual framed parameter field satisfies the exceptional-prime bound. -/
theorem hardlyFramedParameterField_uniform_different_bound (f : H ⟶ A)
    (P : Ideal (NumberField.RingOfIntegers (hardlyFramedParameterField O hp hdim ρ hρ A f)))
    [P.IsPrime] (q : ℕ) (hq : q.Prime)
    (hqP : (q : NumberField.RingOfIntegers (hardlyFramedParameterField O hp hdim ρ hρ A f)) ∈ P) :
    NumberField.differentExponentAt (hardlyFramedParameterField O hp hdim ρ hρ A f) P ≤
      (Nat.card (GL (Fin 2) A) + 1) * P.ramificationIdx ℤ :=
  NumberField.differentExponentAt_le_degree_bound _ _
    (hardlyFramedParameterField_degree_le O hp hdim ρ hρ A f) P q hq hqP

/-- An explicit discriminant bound for the actual framed parameter field. -/
theorem hardlyFramedParameterField_uniform_discr_bound (f : H ⟶ A) :
    |NumberField.discr (hardlyFramedParameterField O hp hdim ρ hρ A f)| ≤
      ((2 * p) ^ ((Nat.card (GL (Fin 2) A) + 1) * Nat.card (GL (Fin 2) A)) : ℕ) := by
  have h2p : 2 ≠ p := by
    rintro rfl
    norm_num at hp
  have h := hardlyFramedParameterField_discr_le O hp hdim ρ hρ A
    (fun _ ↦ Nat.card (GL (Fin 2) A) + 1) (by
      intro g P _ q hq hqP
      apply hardlyFramedParameterField_uniform_different_bound O hp hdim ρ hρ A g P q _ hqP
      simp only [Finset.mem_insert, Finset.mem_singleton] at hq
      rcases hq with rfl | rfl
      · exact Nat.prime_two
      · exact Fact.out) f
  simpa only [Finset.prod_pair h2p,
    ← mul_pow, ← pow_mul] using h

/-- There are finitely many framed coefficient maps to any finite discrete test ring. -/
theorem finite_hardlyFramedParameters : Finite (H ⟶ A) :=
  finite_hardlyFramedParameters_of_discr_bound O hp hdim ρ hρ A _
    (hardlyFramedParameterField_uniform_discr_bound O hp hdim ρ hρ A)

/-- The actual trace parameter field satisfies the exceptional-prime bound. -/
theorem hardlyTraceParameterField_uniform_different_bound (f : T ⟶ A)
    (P : Ideal (NumberField.RingOfIntegers (hardlyTraceParameterField O hp hdim ρ hρ hirr A f)))
    [P.IsPrime] (q : ℕ) (hq : q.Prime)
    (hqP : (q : NumberField.RingOfIntegers
      (hardlyTraceParameterField O hp hdim ρ hρ hirr A f)) ∈ P) :
    NumberField.differentExponentAt (hardlyTraceParameterField O hp hdim ρ hρ hirr A f) P ≤
      (Nat.card (GL (Fin 2) A) + 1) * P.ramificationIdx ℤ :=
  NumberField.differentExponentAt_le_degree_bound _ _
    (hardlyTraceParameterField_degree_le O hp hdim ρ hρ hirr A f) P q hq hqP

/-- An explicit discriminant bound for the actual trace parameter field. -/
theorem hardlyTraceParameterField_uniform_discr_bound (f : T ⟶ A) :
    |NumberField.discr (hardlyTraceParameterField O hp hdim ρ hρ hirr A f)| ≤
      ((2 * p) ^ ((Nat.card (GL (Fin 2) A) + 1) * Nat.card (GL (Fin 2) A)) : ℕ) := by
  have h2p : 2 ≠ p := by
    rintro rfl
    norm_num at hp
  have h := hardlyTraceParameterField_discr_le O hp hdim ρ hρ hirr A
    (fun _ ↦ Nat.card (GL (Fin 2) A) + 1) (by
      intro g P _ q hq hqP
      apply hardlyTraceParameterField_uniform_different_bound O hp hdim ρ hρ hirr A g P q _ hqP
      simp only [Finset.mem_insert, Finset.mem_singleton] at hq
      rcases hq with rfl | rfl
      · exact Nat.prime_two
      · exact Fact.out) f
  simpa only [Finset.prod_pair h2p,
    ← mul_pow, ← pow_mul] using h

include hirr in
/-- There are finitely many trace coefficient maps to any finite discrete test ring. -/
theorem finite_hardlyTraceParameters : Finite (T ⟶ A) :=
  finite_hardlyTraceParameters_of_discr_bound O hp hdim ρ hρ hirr A _
    (hardlyTraceParameterField_uniform_discr_bound O hp hdim ρ hρ hirr A)

end Deformation
