/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.AbsoluteInvariant
public import FLT.LocalClassFieldTheory.UnramifiedAbsoluteSquare

/-!
# Absolute invariants and restriction

Surjectivity of unramified inflation extends the proved unramified
base-change formula to every absolute class. Restriction is the actual
map on continuous Galois cohomology, not a transported invariant formula.
-/

@[expose] public noncomputable section

namespace LocalClassFieldTheory

open IsLocalRing CategoryTheory

variable (R S K C : Type)
  [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
  [Algebra R S] [Module.Finite R S] [FaithfulSMul R S]
  [Field K] [Algebra R K] [IsFractionRing R K]
  [Field C] [Algebra K C] [Algebra R C] [IsScalarTower R K C]
  (E : IntermediateField K C)
  [Algebra S E] [IsFractionRing S E] [Algebra S C] [IsScalarTower S E C]
  [IsScalarTower R S C] [IsScalarTower R S E]
  [Algebra.IsSeparable K C] [IsSepClosed C]
  [Finite (ResidueField R)] [Finite (ResidueField S)]
  [IsAdicComplete (maximalIdeal R) R] [IsAdicComplete (maximalIdeal S) S]

local notation "A" => maximalUnramified R K C
local notation "B" => maximalUnramified S E C

attribute [local instance] unramifiedUnionGalois fieldUnitAction
  unramifiedFieldUnitTopology unramifiedFieldUnitDiscrete
  separableClosureGalois separableClosureUnitTopology separableClosureUnitDiscrete

attribute [local instance] relativeBaseTower

variable [FiniteDimensional K E] [CharZero C]
  (p : ℕ) [Fact p.Prime] [CharP (ResidueField R) p] [CharP (ResidueField S) p]

/-- Actual restriction multiplies the absolute invariant by the finite extension degree. -/
theorem absoluteInvariant_restriction
    (x : continuousCohomology ℤ Gal(C/K) (Additive Cˣ) 2) :
    absoluteInvariant S E C p ((absoluteRestriction K C E 2).hom x) =
      Module.finrank K E • absoluteInvariant R K C p x := by
  obtain ⟨y, rfl⟩ := unramifiedMultiplicativeInflationH2_surjective R K C p x
  have h := congrArg (fun f => f.hom y) (unramifiedAbsolute_cohomology R S K C E 2)
  change (unramifiedMultiplicativeInflation S E C 2).hom
      ((unramifiedBaseChangeCohomology R S K E C 2).hom y) =
    (absoluteRestriction K C E 2).hom ((unramifiedMultiplicativeInflation R K C 2).hom y) at h
  rw [← h, absoluteInvariant_inflation, absoluteInvariant_inflation,
    unramifiedMultiplicativeInvariant_baseChange]

end LocalClassFieldTheory
