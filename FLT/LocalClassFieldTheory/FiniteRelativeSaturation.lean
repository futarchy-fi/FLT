/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.RelativeLowerBound
public import FLT.LocalClassFieldTheory.RelativeOrderInduction

/-!
# Finite relative order and unramified saturation

The degree upper bound and the constructed degree-sized subgroup give the
exact order. Thus every finite relative class is represented by a degree-torsion
unramified class after inflation to the separable closure.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace LocalClassFieldTheory

open IsLocalRing CategoryTheory

variable (R S K C : Type)
  [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
  [Algebra R S] [Module.Finite R S] [FaithfulSMul R S]
  [Field K] [Algebra R K] [IsFractionRing R K]
  [Field C] [Algebra K C] [Algebra R C] [IsScalarTower R K C]
  (E : IntermediateField K C) [IsGalois K E]
  [Algebra S E] [IsFractionRing S E] [Algebra S C] [IsScalarTower S E C]
  [IsScalarTower R S E] [IsScalarTower R S C]
  [Algebra.IsSeparable K C] [IsSepClosed C]
  [Finite (ResidueField R)] [Finite (ResidueField S)]
  [IsAdicComplete (maximalIdeal R) R] [IsAdicComplete (maximalIdeal S) S]

local notation "A" => maximalUnramified R K C
local notation "B" => maximalUnramified S E C
local notation "N" => (MonoidHom.ker (AlgEquiv.restrictNormalHom E : Gal(C/K) →* Gal(E/K)))

attribute [local instance] relativeBaseTower unramifiedUnionGalois fieldUnitAction
  unramifiedFieldUnitTopology unramifiedFieldUnitDiscrete
  separableClosureGalois separableClosureUnitTopology separableClosureUnitDiscrete

variable [FiniteDimensional K E]

local notation "d" => Module.finrank K E

variable [TopologicalSpace (Additive Eˣ)] [DiscreteTopology (Additive Eˣ)]

variable [CharZero E] (p : ℕ) [Fact p.Prime] [CharP (ResidueField S) p]

omit [FaithfulSMul R S] [Algebra S C] [IsScalarTower S E C] [IsScalarTower R S C]
  [IsSepClosed C] [Finite (ResidueField R)] in
include R S p in
/-- Continuous relative H² is finite, by the proved degree induction. -/
theorem finiteRelative_H2_finite :
    Finite (continuousCohomology ℤ Gal(E/K) (Additive Eˣ) 2) := by
  let : IsIntegralClosure S R E := IsIntegralClosure.of_isIntegrallyClosed S R E
  let := (localRelative_H2_finite_and_card_le R S K E p).1
  let e : continuousCohomology ℤ Gal(E/K) (Additive Eˣ) 2 ≅
      groupCohomology (Rep.ofAlgebraAutOnUnits K E) 2 :=
    finiteContinuousCohomologyIso ℤ Gal(E/K) (Additive Eˣ) 2
  exact Finite.of_equiv _ e.toLinearEquiv.toEquiv.symm

include R S p in
/-- The actual relative H² has exactly the degree order. -/
theorem finiteRelative_H2_card :
    Nat.card (continuousCohomology ℤ Gal(E/K) (Additive Eˣ) 2) = d := by
  let : IsIntegralClosure S R E := IsIntegralClosure.of_isIntegrallyClosed S R E
  let := finiteRelative_H2_finite R S K C E p
  apply le_antisymm
  · rw [Nat.card_congr
      (finiteContinuousCohomologyIso ℤ Gal(E/K) (Additive Eˣ) 2).toLinearEquiv.toEquiv]
    exact (localRelative_H2_finite_and_card_le R S K E p).2
  · simpa only [Nat.card_zmod] using Nat.card_le_card_of_injective _
      (relativeLowerBound_injective R S K C E)

include R S p in
/-- Degree-torsion classes exhaust finite relative H². -/
theorem relativeDegreeTorsionHom_surjective :
    Function.Surjective (relativeDegreeTorsionHom R S K C E) := by
  let := finiteRelative_H2_finite R S K C E p
  let : NeZero d := ⟨Module.finrank_pos.ne'⟩
  apply ((relativeDegreeTorsionHom_injective R S K C E).bijective_of_nat_card_le ?_).2
  rw [finiteRelative_H2_card R S K C E p, card_relativeRestrictionKernel]

include R S p in
/-- Every relative class inflates from an actual unramified class. -/
theorem finiteRelative_unramified_saturation
    (x : continuousCohomology ℤ Gal(E/K) (Additive Eˣ) 2) :
    ∃ y, (unramifiedMultiplicativeInflation R K C 2).hom y =
      (galoisMultiplicativeInflation K C E 2).hom x := by
  obtain ⟨z, rfl⟩ := relativeDegreeTorsionHom_surjective R S K C E p x
  exact ⟨(unramifiedMultiplicativeInvariant R K C).symm z.val,
    (relativeDegreeTorsionClass_inflation R S K C E z).symm⟩

end LocalClassFieldTheory
