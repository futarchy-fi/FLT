/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.CyclicRelativeOrder
public import FLT.LocalClassFieldTheory.IntermediateDvr
public import FLT.LocalClassFieldTheory.LocalGaloisSolvable
public import FLT.LocalClassFieldTheory.FiniteRelativeSequence
public import FLT.LocalClassFieldTheory.SolvableFieldStep

/-!
# The upper bound on finite relative H²

Strong induction on the field degree uses a proper normal subgroup of the
proved solvable local Galois group. The actual relative exact sequence and
cyclic order computation give finiteness and the degree upper bound.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace LocalClassFieldTheory

open IsLocalRing CategoryTheory

attribute [local instance] fieldUnitAction intermediateDvrAlgebra

variable (R S K L : Type)
  [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
  [Algebra R S] [Module.Finite R S]
  [Field K] [Algebra R K] [IsFractionRing R K]
  [Field L] [Algebra S L] [IsFractionRing S L] [Algebra K L] [Algebra R L]
  [IsScalarTower R K L] [IsScalarTower R S L]
  [FiniteDimensional K L] [IsGalois K L] [CharZero L]
  [IsAdicComplete (maximalIdeal R) R] [IsAdicComplete (maximalIdeal S) S]
  (p : ℕ) [Fact p.Prime] [CharP (ResidueField S) p]

variable [IsIntegralClosure S R L] [Finite (ResidueField S)]

include R S p in
/-- Finite relative multiplicative H² has at most the extension degree many elements. -/
theorem localRelative_H2_finite_and_card_le :
    Finite (groupCohomology (Rep.ofAlgebraAutOnUnits K L) 2) ∧
      Nat.card (groupCohomology (Rep.ofAlgebraAutOnUnits K L) 2) ≤ Module.finrank K L := by
  classical
  induction hn : Module.finrank K L using Nat.strong_induction_on generalizing R S K L with
  | h n ih =>
    by_cases hc : IsCyclic Gal(L/K)
    · let := hc
      obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Gal(L/K))
      exact ⟨cyclicRelative_H2_finite R S K L p g hg,
        ((cyclicRelative_H2_card R S K L p g hg).trans hn).le⟩
    · let : FaithfulSMul R S := by
        apply (faithfulSMul_iff_algebraMap_injective R S).mpr
        intro a b h
        apply IsFractionRing.injective R K
        apply (algebraMap K L).injective
        simpa only [← IsScalarTower.algebraMap_apply] using congrArg (algebraMap S L) h
      let : Group.IsSolvable Gal(L/K) := localGalois_solvable S p R K L
      obtain ⟨E, hE, hleft, hright⟩ := solvableGalois_smaller_tower K L hc
      let := hE
      let T := integralClosure R E
      let : IsLocalRing T := intermediateDvrLocal R S K L E
      let : Finite (ResidueField T) := intermediateDvrResidueFinite R S K L E
      let : CharP (ResidueField T) p := intermediateDvrResidueChar R S K L E p
      let : CharZero E := ⟨fun m n h => by
        apply Nat.cast_injective (R := L)
        simpa only [map_natCast] using congrArg (algebraMap E L) h⟩
      have hl := ih (Module.finrank K E) (by omega) R T K E rfl
      have hr := ih (Module.finrank E L) (by omega) T S E L rfl
      let := hl.1
      let := hr.1
      let : TopologicalSpace (Additive Lˣ) := ⊥
      let : DiscreteTopology (Additive Lˣ) := ⟨rfl⟩
      let : TopologicalSpace (Additive Eˣ) := ⊥
      let : DiscreteTopology (Additive Eˣ) := ⟨rfl⟩
      let eL : continuousCohomology ℤ Gal(L/K) (Additive Lˣ) 2 ≅
          groupCohomology (Rep.ofAlgebraAutOnUnits K L) 2 :=
        finiteContinuousCohomologyIso ℤ Gal(L/K) (Additive Lˣ) 2
      let eE : continuousCohomology ℤ Gal(E/K) (Additive Eˣ) 2 ≅
          groupCohomology (Rep.ofAlgebraAutOnUnits K E) 2 :=
        finiteContinuousCohomologyIso ℤ Gal(E/K) (Additive Eˣ) 2
      let : Finite (continuousCohomology ℤ Gal(E/K) (Additive Eˣ) 2) :=
        Finite.of_equiv _ eE.toLinearEquiv.toEquiv.symm
      let X := finiteRelativeSequence K L E
      let : Finite X.X₁ :=
        inferInstanceAs (Finite (continuousCohomology ℤ Gal(E/K) (Additive Eˣ) 2))
      let : Finite X.X₃ := hr.1
      have hX : X.Exact := finiteRelativeSequence_exact K L E
      let : Finite X.X₂ := exactSequence_middle_finite X hX
      let : Finite (continuousCohomology ℤ Gal(L/K) (Additive Lˣ) 2) :=
        inferInstanceAs (Finite X.X₂)
      refine ⟨Finite.of_equiv _ eL.toLinearEquiv.toEquiv, ?_⟩
      calc
        _ = Nat.card X.X₂ := Nat.card_congr eL.toLinearEquiv.toEquiv.symm
        _ ≤ Nat.card X.X₁ * Nat.card X.X₃ := exactSequence_card_le X hX
        _ = Nat.card (groupCohomology (Rep.ofAlgebraAutOnUnits K E) 2) *
            Nat.card (groupCohomology (Rep.ofAlgebraAutOnUnits E L) 2) := by
          rw [← Nat.card_congr eE.toLinearEquiv.toEquiv]
          rfl
        _ ≤ Module.finrank K E * Module.finrank E L := Nat.mul_le_mul hl.2 hr.2
        _ = _ := (Module.finrank_mul_finrank K E L).trans hn

end LocalClassFieldTheory
