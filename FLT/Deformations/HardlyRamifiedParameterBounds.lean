/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Deformations.HardlyRamifiedParameterUnramified
public import FLT.NumberField.FinitePrimeDiscriminantBound

/-!
# HR parameter finiteness from exceptional-prime different bounds

Unramifiedness away from 2p is proved for these exact fields. Thus bounds for
the normalized different exponents at the exceptional primes suffice for
Hermite finiteness of coefficient maps. The local bounds are not asserted.
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

/-- The degree bound and exceptional-prime exponent bounds give a uniform discriminant bound. -/
theorem hardlyFramedParameterField_discr_le (c : ℕ → ℕ)
    (hc : ∀ (f : H ⟶ A)
      (P : Ideal (NumberField.RingOfIntegers (hardlyFramedParameterField O hp hdim ρ hρ A f)))
      [P.IsPrime],
      ∀ q ∈ ({2, p} : Finset ℕ), (q : NumberField.RingOfIntegers
        (hardlyFramedParameterField O hp hdim ρ hρ A f)) ∈ P →
        NumberField.differentExponentAt (hardlyFramedParameterField O hp hdim ρ hρ A f) P ≤
          c q * P.ramificationIdx ℤ)
    (f : H ⟶ A) :
    |NumberField.discr (hardlyFramedParameterField O hp hdim ρ hρ A f)| ≤
      ((∏ q ∈ ({2, p} : Finset ℕ), q ^ c q) ^ Nat.card (GL (Fin 2) A) : ℕ) := by
  have hpS : ∀ q ∈ ({2, p} : Finset ℕ), q.Prime := by
    intro q hq
    simp only [Finset.mem_insert, Finset.mem_singleton] at hq
    rcases hq with rfl | rfl
    · exact Nat.prime_two
    · exact Fact.out
  have hlocal := NumberField.natAbs_discr_le_of_exponent_bounds
    (hardlyFramedParameterField O hp hdim ρ hρ A f) ({2, p} : Finset ℕ) c hpS (hc f)
    (fun P _ hP ↦ hardlyFramedParameterField_isUnramifiedAt O hp hdim ρ hρ A f P
      (hP 2 (by simp)) (hP p (by simp)))
  have hpos : 0 < ∏ q ∈ ({2, p} : Finset ℕ), q ^ c q :=
    Finset.prod_pos (fun q hq ↦ pow_pos (hpS q hq).pos _)
  have hle := hlocal.trans (Nat.pow_le_pow_right hpos
    (hardlyFramedParameterField_degree_le O hp hdim ρ hρ A f))
  simpa only [Int.natCast_natAbs] using (Int.ofNat_le.mpr hle)

/-- Local different bounds at 2 and p give finite framed coefficient parameters. -/
theorem finite_hardlyFramedParameters_of_different_bounds (c : ℕ → ℕ)
    (hc : ∀ (f : H ⟶ A)
      (P : Ideal (NumberField.RingOfIntegers (hardlyFramedParameterField O hp hdim ρ hρ A f)))
      [P.IsPrime],
      ∀ q ∈ ({2, p} : Finset ℕ), (q : NumberField.RingOfIntegers
        (hardlyFramedParameterField O hp hdim ρ hρ A f)) ∈ P →
        NumberField.differentExponentAt (hardlyFramedParameterField O hp hdim ρ hρ A f) P ≤
          c q * P.ramificationIdx ℤ) :
    Finite (H ⟶ A) :=
  finite_hardlyFramedParameters_of_discr_bound O hp hdim ρ hρ A
    ((∏ q ∈ ({2, p} : Finset ℕ), q ^ c q) ^ Nat.card (GL (Fin 2) A))
    (hardlyFramedParameterField_discr_le O hp hdim ρ hρ A c hc)

/-- The degree bound and exceptional-prime exponent bounds give a uniform discriminant bound. -/
theorem hardlyTraceParameterField_discr_le (c : ℕ → ℕ)
    (hc : ∀ (f : T ⟶ A)
      (P : Ideal (NumberField.RingOfIntegers (hardlyTraceParameterField O hp hdim ρ hρ hirr A f)))
      [P.IsPrime],
      ∀ q ∈ ({2, p} : Finset ℕ), (q : NumberField.RingOfIntegers
        (hardlyTraceParameterField O hp hdim ρ hρ hirr A f)) ∈ P →
        NumberField.differentExponentAt (hardlyTraceParameterField O hp hdim ρ hρ hirr A f) P ≤
          c q * P.ramificationIdx ℤ)
    (f : T ⟶ A) :
    |NumberField.discr (hardlyTraceParameterField O hp hdim ρ hρ hirr A f)| ≤
      ((∏ q ∈ ({2, p} : Finset ℕ), q ^ c q) ^ Nat.card (GL (Fin 2) A) : ℕ) := by
  have hpS : ∀ q ∈ ({2, p} : Finset ℕ), q.Prime := by
    intro q hq
    simp only [Finset.mem_insert, Finset.mem_singleton] at hq
    rcases hq with rfl | rfl
    · exact Nat.prime_two
    · exact Fact.out
  have hlocal := NumberField.natAbs_discr_le_of_exponent_bounds
    (hardlyTraceParameterField O hp hdim ρ hρ hirr A f) ({2, p} : Finset ℕ) c hpS (hc f)
    (fun P _ hP ↦ hardlyTraceParameterField_isUnramifiedAt O hp hdim ρ hρ hirr A f P
      (hP 2 (by simp)) (hP p (by simp)))
  have hpos : 0 < ∏ q ∈ ({2, p} : Finset ℕ), q ^ c q :=
    Finset.prod_pos (fun q hq ↦ pow_pos (hpS q hq).pos _)
  have hle := hlocal.trans (Nat.pow_le_pow_right hpos
    (hardlyTraceParameterField_degree_le O hp hdim ρ hρ hirr A f))
  simpa only [Int.natCast_natAbs] using (Int.ofNat_le.mpr hle)

/-- Local different bounds at 2 and p give finite trace coefficient parameters. -/
theorem finite_hardlyTraceParameters_of_different_bounds (c : ℕ → ℕ)
    (hc : ∀ (f : T ⟶ A)
      (P : Ideal (NumberField.RingOfIntegers (hardlyTraceParameterField O hp hdim ρ hρ hirr A f)))
      [P.IsPrime],
      ∀ q ∈ ({2, p} : Finset ℕ), (q : NumberField.RingOfIntegers
        (hardlyTraceParameterField O hp hdim ρ hρ hirr A f)) ∈ P →
        NumberField.differentExponentAt (hardlyTraceParameterField O hp hdim ρ hρ hirr A f) P ≤
          c q * P.ramificationIdx ℤ) :
    Finite (T ⟶ A) :=
  finite_hardlyTraceParameters_of_discr_bound O hp hdim ρ hρ hirr A
    ((∏ q ∈ ({2, p} : Finset ℕ), q ^ c q) ^ Nat.card (GL (Fin 2) A))
    (hardlyTraceParameterField_discr_le O hp hdim ρ hρ hirr A c hc)

end Deformation
