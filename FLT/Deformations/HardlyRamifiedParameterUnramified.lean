/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Deformations.HardlyRamifiedFiniteParameters
public import FLT.Deformations.HardlyRamifiedFramedParameters
public import FLT.AbsoluteGaloisGroup.FiniteImageUnramified
public import FLT.NumberField.UnramifiedPrimeSupport

/-!
# Unramifiedness of the actual HR parameter fields

Both framed and trace specializations have kernel fields unramified outside
2p. Consequently their absolute different is supported over 2 and p.
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
variable (A : ProartinianCat O) [DiscreteTopology A]

/-- The exact framed kernel field is unramified at every prime away from 2p. -/
theorem hardlyFramedParameterField_isUnramifiedIn (f : H ⟶ A)
    (q : ℕ) (hq : q.Prime) (hq2 : q ≠ 2) (hqp : q ≠ p) :
    Algebra.IsUnramifiedIn
      (NumberField.RingOfIntegers (hardlyFramedParameterField O hp hdim ρ hρ A f))
      hq.toHeightOneSpectrumRingOfIntegersRat.asIdeal := by
  apply finiteImageField_isUnramifiedIn
  intro s hs
  apply hardlyFramedParameterRepresentation_inertia O hp hdim ρ hρ A f
  refine ⟨q, hq, hq2, hqp, s, hs, ?_⟩
  exact congrArg (fun k : ℚ →+* hq.toHeightOneSpectrumRingOfIntegersRat.adicCompletion ℚ ↦
    Field.absoluteGaloisGroup.map k s) (Subsingleton.elim _ _)

/-- Absolute unramifiedness of framed parameter fields outside 2p, over `ℤ`. -/
theorem hardlyFramedParameterField_isUnramifiedAt (f : H ⟶ A)
    (P : Ideal (NumberField.RingOfIntegers (hardlyFramedParameterField O hp hdim ρ hρ A f)))
    [P.IsPrime] (h2 : (2 : NumberField.RingOfIntegers
      (hardlyFramedParameterField O hp hdim ρ hρ A f)) ∉ P)
    (hpP : (p : NumberField.RingOfIntegers
      (hardlyFramedParameterField O hp hdim ρ hρ A f)) ∉ P) :
    Algebra.IsUnramifiedAt ℤ P := by
  apply NumberField.isUnramifiedAt_int_of_unramifiedOutside _ ({2, p} : Finset ℕ)
  · intro q hq hqS
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hqS
    exact hardlyFramedParameterField_isUnramifiedIn O hp hdim ρ hρ A f q hq hqS.1 hqS.2
  · intro q hq
    simp only [Finset.mem_insert, Finset.mem_singleton] at hq
    rcases hq with rfl | rfl
    · exact h2
    · exact hpP

/-- Different exponents of the actual framed field vanish away from 2p. -/
theorem hardlyFramedParameterField_differentExponent_eq_zero (f : H ⟶ A)
    (P : Ideal (NumberField.RingOfIntegers (hardlyFramedParameterField O hp hdim ρ hρ A f)))
    [P.IsPrime] (h2 : (2 : NumberField.RingOfIntegers
      (hardlyFramedParameterField O hp hdim ρ hρ A f)) ∉ P)
    (hpP : (p : NumberField.RingOfIntegers
      (hardlyFramedParameterField O hp hdim ρ hρ A f)) ∉ P) :
    NumberField.differentExponentAt (hardlyFramedParameterField O hp hdim ρ hρ A f) P = 0 :=
  NumberField.differentExponentAt_eq_zero_of_isUnramifiedAt _ P
    (hardlyFramedParameterField_isUnramifiedAt O hp hdim ρ hρ A f P h2 hpP)

/-- The exact trace kernel field is unramified at every prime away from 2p. -/
theorem hardlyTraceParameterField_isUnramifiedIn (f : T ⟶ A)
    (q : ℕ) (hq : q.Prime) (hq2 : q ≠ 2) (hqp : q ≠ p) :
    Algebra.IsUnramifiedIn
      (NumberField.RingOfIntegers (hardlyTraceParameterField O hp hdim ρ hρ hirr A f))
      hq.toHeightOneSpectrumRingOfIntegersRat.asIdeal := by
  apply finiteImageField_isUnramifiedIn
  intro s hs
  apply hardlyTraceParameterRepresentation_inertia O hp hdim ρ hρ hirr A f
  refine ⟨q, hq, hq2, hqp, s, hs, ?_⟩
  exact congrArg (fun k : ℚ →+* hq.toHeightOneSpectrumRingOfIntegersRat.adicCompletion ℚ ↦
    Field.absoluteGaloisGroup.map k s) (Subsingleton.elim _ _)

/-- Absolute unramifiedness of trace parameter fields outside 2p, over `ℤ`. -/
theorem hardlyTraceParameterField_isUnramifiedAt (f : T ⟶ A)
    (P : Ideal (NumberField.RingOfIntegers (hardlyTraceParameterField O hp hdim ρ hρ hirr A f)))
    [P.IsPrime] (h2 : (2 : NumberField.RingOfIntegers
      (hardlyTraceParameterField O hp hdim ρ hρ hirr A f)) ∉ P)
    (hpP : (p : NumberField.RingOfIntegers
      (hardlyTraceParameterField O hp hdim ρ hρ hirr A f)) ∉ P) :
    Algebra.IsUnramifiedAt ℤ P := by
  apply NumberField.isUnramifiedAt_int_of_unramifiedOutside _ ({2, p} : Finset ℕ)
  · intro q hq hqS
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hqS
    exact hardlyTraceParameterField_isUnramifiedIn O hp hdim ρ hρ hirr A f q hq hqS.1 hqS.2
  · intro q hq
    simp only [Finset.mem_insert, Finset.mem_singleton] at hq
    rcases hq with rfl | rfl
    · exact h2
    · exact hpP

/-- Different exponents of the actual trace field vanish away from 2p. -/
theorem hardlyTraceParameterField_differentExponent_eq_zero (f : T ⟶ A)
    (P : Ideal (NumberField.RingOfIntegers (hardlyTraceParameterField O hp hdim ρ hρ hirr A f)))
    [P.IsPrime] (h2 : (2 : NumberField.RingOfIntegers
      (hardlyTraceParameterField O hp hdim ρ hρ hirr A f)) ∉ P)
    (hpP : (p : NumberField.RingOfIntegers
      (hardlyTraceParameterField O hp hdim ρ hρ hirr A f)) ∉ P) :
    NumberField.differentExponentAt (hardlyTraceParameterField O hp hdim ρ hρ hirr A f) P = 0 :=
  NumberField.differentExponentAt_eq_zero_of_isUnramifiedAt _ P
    (hardlyTraceParameterField_isUnramifiedAt O hp hdim ρ hρ hirr A f P h2 hpP)

end Deformation
