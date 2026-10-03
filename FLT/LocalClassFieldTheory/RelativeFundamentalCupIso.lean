/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.RelativeFundamentalAcyclic

/-!
# The local fundamental cup isomorphism

All-degree acyclicity of the actual middle term makes the first boundary
invertible. Composing it with the constructed coinduced shift proves the
fundamental cup isomorphism, including input degree minus two.
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
  (F : IntermediateField K C) [IsGalois K F] [FiniteDimensional K F]
  [Algebra S F] [IsFractionRing S F] [Algebra S C] [IsScalarTower S F C]
  [IsScalarTower R S F] [IsScalarTower R S C]
  [Algebra.IsSeparable K C] [IsSepClosed C]
  [Finite (ResidueField R)] [Finite (ResidueField S)]
  [IsAdicComplete (maximalIdeal R) R] [IsAdicComplete (maximalIdeal S) S]

attribute [local instance] relativeBaseTower unramifiedUnionGalois fieldUnitAction
  unramifiedFieldUnitTopology unramifiedFieldUnitDiscrete
  separableClosureGalois separableClosureUnitTopology separableClosureUnitDiscrete

variable [TopologicalSpace (Additive Fˣ)] [DiscreteTopology (Additive Fˣ)]
  [CharZero C] (p : ℕ) [Fact p.Prime]
  [CharP (ResidueField R) p] [CharP (ResidueField S) p]

local notation "M" => Rep.ofAlgebraAutOnUnits K F
local notation "c" => twoClassRepresentative M (relativeFundamentalOrdinaryClass R S K C F)
local notation "hX" => oneCocycleSequence_shortExact (shiftedCoefficients M) (shiftedTwoCocycle M c)

include p in
/-- The first boundary is invertible because its actual middle term is acyclic. -/
theorem relativeFundamentalExtension_boundary_isIso (n : ℤ) :
    IsIso (TateCohomology.δ hX n) :=
  ShortComplex.SnakeInput.isIso_δ _
    (relativeFundamentalExtension_all_isZero R S K C F p n)
    (relativeFundamentalExtension_all_isZero R S K C F p (n + 1))

include p in
/-- Cup with the local fundamental class is an isomorphism in every Tate degree. -/
theorem relativeFundamentalTateCup_isIso (n : ℤ) :
    IsIso (relativeFundamentalTateCup R S K C F n) := by
  change IsIso (tateTwoExtensionMap M c n)
  rw [tateTwoExtensionMap_eq_shift]
  have := relativeFundamentalExtension_boundary_isIso R S K C F p n
  infer_instance

/-- The proved local fundamental cup equivalence in every integer degree. -/
def relativeFundamentalTateCupIso (n : ℤ) :
    tateCohomology (Rep.trivial ℤ Gal(F/K) ℤ) n ≅ tateCohomology M (n + 2) := by
  have := relativeFundamentalTateCup_isIso R S K C F p n
  exact asIso (relativeFundamentalTateCup R S K C F n)

/-- The actual degree-minus-two cup identifies scalar homology with the norm quotient. -/
def relativeFundamentalTateCupNegTwoEquiv :
    tateCohomology (Rep.trivial ℤ Gal(F/K) ℤ) (-2) ≃ₗ[ℤ] tateCohomology M 0 :=
  (relativeFundamentalTateCupIso R S K C F p (-2)).toLinearEquiv

/-- The forward map of the degree-minus-two equivalence is the constructed cup. -/
theorem relativeFundamentalTateCupNegTwoEquiv_apply
    (x : tateCohomology (Rep.trivial ℤ Gal(F/K) ℤ) (-2)) :
    relativeFundamentalTateCupNegTwoEquiv R S K C F p x =
      relativeFundamentalTateCup R S K C F (-2) x := rfl

end LocalClassFieldTheory
