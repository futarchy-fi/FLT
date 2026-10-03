/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.FundamentalClasses
public import Mathlib.RepresentationTheory.Homological.TateCohomology.Basic

/-!
# Positive Tate cohomology of a finite local extension

Finite continuous comparison and the Tate complex comparison transport the
proved relative generator to actual Tate H2. Hilbert 90 gives Tate H1 = 0.
These are inputs to class formation; no cup-product isomorphism is assumed.
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

variable [CharZero C] (p : ℕ) [Fact p.Prime]
  [CharP (ResidueField R) p] [CharP (ResidueField S) p]

/-- The actual continuous relative group agrees with positive Tate cohomology. -/
def relativePositiveTateEquiv (n : ℕ) [NeZero n] :
    continuousCohomology ℤ Gal(E/K) (Additive Eˣ) n ≃+
      tateCohomology (Rep.ofAlgebraAutOnUnits K E) n :=
  ((finiteContinuousCohomologyIso ℤ Gal(E/K) (Additive Eˣ) n) ≪≫
    ((TateCohomology.isoGroupCohomology n).app (Rep.ofAlgebraAutOnUnits K E)).symm
      ).toLinearEquiv.toAddEquiv

omit [CharP (ResidueField R) p] in
/-- Relative H2 is cyclic with the prescribed fundamental generator. -/
def relativeFundamentalEquiv : ZMod d ≃+
    continuousCohomology ℤ Gal(E/K) (Additive Eˣ) 2 :=
  AddEquiv.ofBijective (relativeLowerBound R S K C E)
    ⟨relativeLowerBound_injective R S K C E, relativeLowerBound_surjective R S K C E p⟩

omit [CharP (ResidueField R) p] in
/-- Actual Tate H2 is cyclic of extension-degree order. -/
def relativeTateH2Equiv : ZMod d ≃+ tateCohomology (Rep.ofAlgebraAutOnUnits K E) 2 :=
  (relativeFundamentalEquiv R S K C E p).trans (relativePositiveTateEquiv K C E 2)

omit [IsGalois K E] [Algebra.IsSeparable K C] [IsSepClosed C]
  [TopologicalSpace (Additive Eˣ)] [DiscreteTopology (Additive Eˣ)] [CharZero C] in
/-- Hilbert 90 vanishes in the actual Tate complex in degree one. -/
theorem relativeTateH1_eq_zero (x : tateCohomology (Rep.ofAlgebraAutOnUnits K E) 1) :
    x = 0 := by
  apply (((TateCohomology.isoGroupCohomology 1).app
    (Rep.ofAlgebraAutOnUnits K E)).toLinearEquiv).injective
  exact Subsingleton.elim (α := groupCohomology (Rep.ofAlgebraAutOnUnits K E) 1) _ _

omit [CharP (ResidueField R) p] in
/-- The Tate generator is the image of the previously constructed relative fundamental class. -/
theorem relativeTateH2Equiv_one : relativeTateH2Equiv R S K C E p 1 =
    relativePositiveTateEquiv K C E 2 (relativeFundamentalClass R S K C E) := rfl

end LocalClassFieldTheory
