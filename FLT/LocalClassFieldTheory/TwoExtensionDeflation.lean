/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.TateZeroDeflation
public import FLT.LocalClassFieldTheory.TwoCocycleInflationSum
public import FLT.LocalClassFieldTheory.TwoExtensionCorestriction

/-!
# Deflating the negative cup of an inflated class

For a normal subgroup, the actual degree-zero deflation of an inflated
negative cup is the subgroup-order multiple of the quotient cup.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace LocalClassFieldTheory

open CategoryTheory groupCohomology

section Coefficients

variable {k G : Type} [CommRing k] [Group G]
  (M : Rep k G) (N : Subgroup G) [N.Normal]

local notation "MQ" => M.quotientToInvariants N
local notation "q" => QuotientGroup.mk' N

/-- Include subgroup-invariant coefficients after pulling back the quotient action. -/
def quotientInflationCoefficients : Rep.res q MQ ⟶ M :=
  Rep.ofHom (M.ρ.quotientToInvariants_lift N)

/-- Inflation followed by invariant identification recovers the quotient invariant. -/
theorem quotientInvariant_inflation (x : (MQ).ρ.invariants) :
    quotientInvariantEquiv M N
      (inflationInvariant MQ M q (quotientInflationCoefficients M N) x) = x := rfl

end Coefficients

variable {G : Type} [Group G] [Fintype G]
  (M : Rep ℤ G) (N : Subgroup G) [N.Normal] [Fintype (G ⧸ N)]

local notation "MQ" => M.quotientToInvariants N
local notation "q" => QuotientGroup.mk' N
local notation "ι" => quotientInflationCoefficients M N

/-- Deflating the actual negative cup of an inflated cocycle counts the subgroup fibers. -/
theorem tateTwoExtensionMap_deflation_inflation (c : cocycles₂ MQ)
    (x : tateCohomology (Rep.trivial ℤ G ℤ) (-2)) :
    tateZeroDeflation M N (tateTwoExtensionMap M (mapCocycles₂ q ι c) (-2) x) =
      Nat.card N • tateTwoExtensionMap MQ c (-2) (tateScalarMap q x) := by
  obtain ⟨g, rfl⟩ := tateScalarGenerator_surjective G x
  rw [tateScalarMap_generator, tateTwoExtensionMap_generator,
    tateTwoExtensionMap_generator, tateZeroDeflation_class,
    twoCocycleSumInvariant_inflation MQ M q ι (QuotientGroup.mk'_surjective N),
    map_nsmul, quotientInvariant_inflation, QuotientGroup.ker_mk', map_inv]
  exact map_nsmul (tateInvariantClass MQ).hom _ _

/-- The deflation-inflation formula holds on the actual ordinary two-class. -/
theorem tateTwoClassMap_deflation_inflation (a : groupCohomology MQ 2)
    (x : tateCohomology (Rep.trivial ℤ G ℤ) (-2)) :
    tateZeroDeflation M N (tateTwoClassMap M (groupCohomology.map q ι 2 a) (-2) x) =
      Nat.card N • tateTwoClassMap MQ a (-2) (tateScalarMap q x) := by
  obtain ⟨c, rfl⟩ := (ModuleCat.epi_iff_surjective (H2π MQ)).mp inferInstance a
  have hr := congrArg (fun t => t.hom c) (H2π_comp_map q ι)
  change groupCohomology.map q ι 2 (H2π MQ c) = H2π M (mapCocycles₂ q ι c) at hr
  rw [hr, tateTwoClassMap_class, tateTwoClassMap_class]
  exact tateTwoExtensionMap_deflation_inflation M N c x

end LocalClassFieldTheory
