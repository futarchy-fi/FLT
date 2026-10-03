/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.TateScalarQuotientExact
public import FLT.LocalClassFieldTheory.TateZeroDeflationExact
public import FLT.LocalClassFieldTheory.TwoExtensionCorestriction

/-!
# Unscaled descent of the negative cup

Deflation of the negative cup kills the scalar quotient kernel. It therefore
descends uniquely to the quotient's scalar Tate group, including when the
subgroup and quotient orders share a prime. Identifying this descended map
with cup by an independently chosen quotient class is a separate question.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace LocalClassFieldTheory

open CategoryTheory groupCohomology

variable {G : Type} [Group G] [Fintype G]
  (M : Rep ℤ G) (N : Subgroup G) [N.Normal] [Fintype (G ⧸ N)]
  (a : groupCohomology M 2)

local notation "MQ" => M.quotientToInvariants N
local notation "q" => QuotientGroup.mk' N

/-- The scalar quotient kernel is killed by deflation of the actual negative cup. -/
theorem negativeCup_quotient_kernel :
    (tateScalarMap q).ker ≤
      ((tateZeroDeflation M N).toAddMonoidHom.comp
        (tateTwoClassMap M a (-2)).hom.toAddMonoidHom).ker := by
  classical
  let : Fintype N := Fintype.ofFinite N
  intro x hx
  obtain ⟨y, rfl⟩ := (tateScalarMap_quotient_eq_zero_iff N x).mp hx
  change tateZeroDeflation M N (tateTwoClassMap M a (-2) (tateScalarMap N.subtype y)) = 0
  rw [← tateTwoClassMap_corestriction M N a y]
  exact tateZeroDeflation_corestriction M N _

/-- The negative cup descended along the actual group quotient, with no degree factor. -/
def negativeCupQuotient :
    tateCohomology (Rep.trivial ℤ (G ⧸ N) ℤ) (-2) →+ tateCohomology MQ 0 :=
  (tateScalarMap q).liftOfSurjective (tateScalarMap_quotient_surjective N)
    ⟨(tateZeroDeflation M N).toAddMonoidHom.comp
      (tateTwoClassMap M a (-2)).hom.toAddMonoidHom, negativeCup_quotient_kernel M N a⟩

/-- The descended cup satisfies an unscaled square on every ambient Tate class. -/
theorem negativeCupQuotient_scalarMap
    (x : tateCohomology (Rep.trivial ℤ G ℤ) (-2)) :
    negativeCupQuotient M N a (tateScalarMap q x) =
      tateZeroDeflation M N (tateTwoClassMap M a (-2) x) := by
  exact AddMonoidHom.liftOfRightInverse_comp_apply _ _ _ _ x

/-- On a quotient generator, the descended cup is the deflated ambient cocycle sum. -/
theorem negativeCupQuotient_generator (c : cocycles₂ M) (g : G) :
    negativeCupQuotient M N (H2π M c) (tateScalarGenerator ℤ (G ⧸ N) (q g)) =
      tateInvariantClass MQ (quotientInvariantEquiv M N (twoCocycleSumInvariant M c g⁻¹)) := by
  rw [← tateScalarMap_generator, negativeCupQuotient_scalarMap,
    tateTwoClassMap_class, tateTwoExtensionMap_generator, tateZeroDeflation_class]

/-- The unscaled square uniquely determines the descended negative cup. -/
theorem negativeCupQuotient_unique
    (f : tateCohomology (Rep.trivial ℤ (G ⧸ N) ℤ) (-2) →+ tateCohomology MQ 0)
    (hf : ∀ x, f (tateScalarMap q x) =
      tateZeroDeflation M N (tateTwoClassMap M a (-2) x)) :
    f = negativeCupQuotient M N a := by
  ext x
  obtain ⟨y, rfl⟩ := tateScalarMap_quotient_surjective N x
  exact (hf y).trans (negativeCupQuotient_scalarMap M N a y).symm

end LocalClassFieldTheory
