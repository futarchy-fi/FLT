/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.FiniteTowerQuotientCoefficients
public import FLT.LocalClassFieldTheory.TwoExtensionDeflation

/-!
# The actual quotient comparison squares

The quotient group and coefficient maps factor ordinary field inflation.
On Tate H⁰, their transport takes the field-norm projection to deflation.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace LocalClassFieldTheory

open CategoryTheory groupCohomology HomologicalComplex

variable (K E L : Type) [Field K] [Field E] [Field L]
  [Algebra K E] [Algebra K L] [Algebra E L] [IsScalarTower K E L]
  [IsGalois K E] [IsGalois K L] [FiniteDimensional K E] [FiniteDimensional K L]

local notation "ME" => Rep.ofAlgebraAutOnUnits K E
local notation "ML" => Rep.ofAlgebraAutOnUnits K L
local notation "f" => (AlgEquiv.restrictNormalHom E : Gal(L/K) →* Gal(E/K))
local notation "N" => MonoidHom.ker f
local notation "MQ" => Rep.quotientToInvariants ML N
local notation "e" => finiteTowerQuotientGroup K E L
local notation "φ" => finiteTowerQuotientCoefficients K E L
local notation "q" => QuotientGroup.mk' N

omit [FiniteDimensional K E] [FiniteDimensional K L] in
/-- Quotient coefficient transport followed by inflation is ordinary field inflation. -/
theorem finiteTowerQuotient_cochain_square :
    cochainsMap (e).toMonoidHom φ ≫ cochainsMap q (quotientInflationCoefficients ML N) =
      cochainsMap f (finiteTowerCoefficients K E L) := by
  ext n z g
  rfl

omit [FiniteDimensional K E] [FiniteDimensional K L] in
/-- The actual ordinary cohomology inflation factors through the quotient presentation. -/
theorem finiteTowerQuotient_inflation (n : ℕ) (a : groupCohomology ME n) :
    groupCohomology.map q (quotientInflationCoefficients ML N) n
      (groupCohomology.map (e).toMonoidHom φ n a) =
    groupCohomology.map f (finiteTowerCoefficients K E L) n a := by
  change (homologyMap (cochainsMap (e).toMonoidHom φ) n ≫
    homologyMap (cochainsMap q (quotientInflationCoefficients ML N)) n) a = _
  rw [← homologyMap_comp, finiteTowerQuotient_cochain_square]
  rfl

variable [Fintype (Gal(L/K) ⧸
  (AlgEquiv.restrictNormalHom E : Gal(L/K) →* Gal(E/K)).ker)]

omit [Fintype (Gal(L/K) ⧸
  (AlgEquiv.restrictNormalHom E : Gal(L/K) →* Gal(E/K)).ker)] in
/-- Transport of the smaller-field invariant agrees with the quotient invariant. -/
theorem finiteTowerQuotient_invariant (x : (ML).ρ.invariants) :
    groupEquivalenceInvariant ME MQ e φ (finiteTowerInvariantEquiv K E L x) =
      quotientInvariantEquiv ML N x := by
  obtain ⟨u, rfl⟩ := finiteUnitInvariantInclusion_surjective K L x
  rw [finiteTowerInvariantEquiv_unit]
  apply Subtype.ext
  apply Subtype.ext
  apply Additive.toMul.injective
  apply Units.ext
  exact (IsScalarTower.algebraMap_apply K E L (Additive.toMul u : Kˣ)).symm

/-- Transport of the norm-tower projection is the actual Tate deflation. -/
theorem finiteTowerQuotient_deflation (x : tateCohomology ML 0) :
    tateZeroGroupEquivalence ME MQ e φ (finiteTateNormTower K E L x) =
      tateZeroDeflation ML N x := by
  obtain ⟨u, rfl⟩ := tateInvariantClass_surjective ML x
  rw [finiteTateNormTower_class, tateZeroGroupEquivalence_class,
    finiteTowerQuotient_invariant, tateZeroDeflation_class]

/-- The quotient coefficient identification reflects degree-zero Tate equality. -/
theorem finiteTowerQuotient_tate_injective :
    Function.Injective (tateZeroGroupEquivalence ME MQ e φ) :=
  tateZeroGroupEquivalence_injective ME MQ e φ
    ⟨finiteTowerQuotientCoefficients_injective K E L,
      finiteTowerQuotientCoefficients_surjective K E L⟩

/-- The scalar group maps factor by the same quotient equivalence. -/
theorem finiteTowerQuotient_scalar
    (x : tateCohomology (Rep.trivial ℤ Gal(L/K) ℤ) (-2)) :
    tateScalarMap (e).toMonoidHom (tateScalarMap q x) = tateScalarMap f x := by
  obtain ⟨g, rfl⟩ := tateScalarGenerator_surjective Gal(L/K) x
  rw [tateScalarMap_generator, tateScalarMap_generator, tateScalarMap_generator]
  rfl

/-- The smaller-field cup transported to quotient coefficients uses the same scalar projection. -/
theorem finiteTowerQuotient_cup (a : groupCohomology ME 2)
    (x : tateCohomology (Rep.trivial ℤ Gal(L/K) ℤ) (-2)) :
    tateZeroGroupEquivalence ME MQ e φ (tateTwoClassMap ME a (-2) (tateScalarMap f x)) =
      tateTwoClassMap MQ (groupCohomology.map (e).toMonoidHom φ 2 a) (-2)
        (tateScalarMap q x) := by
  rw [← finiteTowerQuotient_scalar K E L x]
  exact tateTwoClassMap_groupEquivalence ME MQ e φ a (tateScalarMap q x)

end LocalClassFieldTheory
