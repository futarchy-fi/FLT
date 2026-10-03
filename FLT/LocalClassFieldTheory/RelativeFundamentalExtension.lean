/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.CoinducedTateShift
public import FLT.LocalClassFieldTheory.RelativeTateCupDegreeZero
public import FLT.LocalClassFieldTheory.TateExactSequence
public import FLT.LocalClassFieldTheory.TateScalarVanishing

/-!
# Low-degree vanishing for the relative fundamental extension

The concrete twisted extension has zero Tate cohomology in degrees zero and
one. The proof uses the established degree-zero cup isomorphism, Hilbert 90,
and the coinduced dimension shift; no invertibility is assumed.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace LocalClassFieldTheory

open IsLocalRing CategoryTheory CategoryTheory.Limits

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

variable [CharZero C] (p : ℕ) [Fact p.Prime] [CharP (ResidueField S) p]

local notation "M" => Rep.ofAlgebraAutOnUnits K E
local notation "c" => twoClassRepresentative M (relativeFundamentalOrdinaryClass R S K C E)
local notation "Q" => shiftedCoefficients M
local notation "b" => shiftedTwoCocycle M c
local notation "X" => oneCocycleSequence Q b
local notation "hX" => oneCocycleSequence_shortExact Q b

/-- The actual twisted coefficient module used by relative fundamental cup. -/
abbrev relativeFundamentalExtension : Rep ℤ Gal(E/K) := oneCocycleExtension Q b

include p in
/-- The first boundary of the relative fundamental extension is injective in degree zero. -/
theorem relativeFundamentalExtension_boundary_injective :
    Function.Injective (TateCohomology.δ hX 0).hom :=
  (tateTwoExtensionMap_injective_iff M c 0).mp
    (relativeFundamentalTateCup_zero_injective R S K C E p)

include p in
/-- The first boundary of the relative fundamental extension is surjective in degree zero. -/
theorem relativeFundamentalExtension_boundary_surjective :
    Function.Surjective (TateCohomology.δ hX 0).hom :=
  (tateTwoExtensionMap_surjective_iff M c 0).mp
    (relativeFundamentalTateCup_zero_surjective R S K C E p)

omit [IsGalois K E] [Algebra.IsSeparable K C] [IsSepClosed C]
  [TopologicalSpace (Additive Eˣ)] [DiscreteTopology (Additive Eˣ)] [CharZero C] in
/-- Hilbert 90 and the actual dimension shift kill degree zero of the coefficient quotient. -/
theorem relativeShiftedTate_zero_isZero : Limits.IsZero (tateCohomology Q 0) := by
  have h : Limits.IsZero (tateCohomology M 1) := by
    apply ModuleCat.isZero_iff_subsingleton.mpr
    exact ⟨fun x y => (relativeTateH1_eq_zero K C E x).trans
      (relativeTateH1_eq_zero K C E y).symm⟩
  exact h.of_iso (coinducedTateShift M 0)

include p in
/-- Degree zero of the relative fundamental twisted extension vanishes. -/
theorem relativeFundamentalExtension_tate_zero_isZero :
    Limits.IsZero (tateCohomology (relativeFundamentalExtension R S K C E) 0) := by
  have : Mono (TateCohomology.δ hX 0) := (ModuleCat.mono_iff_injective _).mpr
    (relativeFundamentalExtension_boundary_injective R S K C E p)
  apply (tateCohomology_exact₂ hX 0).isZero_X₂
  · exact (relativeShiftedTate_zero_isZero K C E).eq_of_src _ _
  · change (tateCohomologyFunctor 0).map (oneCocycleSequence Q b).g = 0
    rw [← cancel_mono (TateCohomology.δ hX 0), TateCohomology.map_δ, zero_comp]

include p in
/-- Degree one of the relative fundamental twisted extension vanishes. -/
theorem relativeFundamentalExtension_tate_one_isZero :
    Limits.IsZero (tateCohomology (relativeFundamentalExtension R S K C E) 1) := by
  have : Epi (TateCohomology.δ hX 0) := (ModuleCat.epi_iff_surjective _).mpr
    (relativeFundamentalExtension_boundary_surjective R S K C E p)
  apply (tateCohomology_exact₂ hX 1).isZero_X₂
  · change (tateCohomologyFunctor (0 + 1)).map (oneCocycleSequence Q b).f = 0
    rw [← cancel_epi (TateCohomology.δ hX 0), TateCohomology.δ_map, comp_zero]
  · exact (tateScalar_one_isZero Gal(E/K)).eq_of_tgt _ _

omit [CharZero C] in
/-- The actual relative cup in degree minus one is bijective between zero groups. -/
theorem relativeFundamentalTateCup_neg_one_bijective :
    Function.Bijective (relativeFundamentalTateCup R S K C E (-1)).hom := by
  have := ModuleCat.isZero_iff_subsingleton.mp (tateScalar_neg_one_isZero Gal(E/K))
  have : Subsingleton (tateCohomology M (-1 + 2)) := by
    rw [show (-1 + 2 : ℤ) = 1 by omega]
    exact ⟨fun x y => (relativeTateH1_eq_zero K C E x).trans
      (relativeTateH1_eq_zero K C E y).symm⟩
  constructor
  · intro x y _
    exact Subsingleton.elim x y
  · intro a
    exact ⟨0, Subsingleton.elim _ _⟩

omit [CharZero C] in
/-- The proved degree-minus-one equivalence has the actual cup as its forward map. -/
def relativeFundamentalTateCupNegOneEquiv :
    tateCohomology (Rep.trivial ℤ Gal(E/K) ℤ) (-1) ≃ₗ[ℤ] tateCohomology M 1 :=
  LinearEquiv.ofBijective (relativeFundamentalTateCup R S K C E (-1)).hom
    (relativeFundamentalTateCup_neg_one_bijective R S K C E)

end LocalClassFieldTheory
