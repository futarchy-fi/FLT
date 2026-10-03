/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.TwoExtensionCorestriction

/-!
# Additivity of the negative two-class operation

The cocycle-sum evaluation proves linearity in the ordinary two-class,
without a choice of compatible representatives.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace LocalClassFieldTheory

open CategoryTheory groupCohomology

variable {G : Type} [Group G] [Fintype G] (M : Rep ℤ G)

/-- The negative cup is additive in its cocycle argument. -/
theorem tateTwoExtensionMap_negTwo_add (c d : cocycles₂ M)
    (x : tateCohomology (Rep.trivial ℤ G ℤ) (-2)) :
    tateTwoExtensionMap M (c + d) (-2) x =
      tateTwoExtensionMap M c (-2) x + tateTwoExtensionMap M d (-2) x := by
  obtain ⟨g, rfl⟩ := tateScalarGenerator_surjective G x
  simp only [tateTwoExtensionMap_generator]
  have he : twoCocycleSumInvariant M (c + d) g⁻¹ =
      twoCocycleSumInvariant M c g⁻¹ + twoCocycleSumInvariant M d g⁻¹ := by
    apply Subtype.ext
    change (∑ h : G, (c (h, g⁻¹) + d (h, g⁻¹))) = _
    exact Finset.sum_add_distrib
  exact (congrArg (tateInvariantClass M) he).trans
    (map_add (tateInvariantClass M).hom _ _)

/-- The negative cup respects natural multiples of a cocycle. -/
theorem tateTwoExtensionMap_negTwo_nsmul (m : ℕ) (c : cocycles₂ M)
    (x : tateCohomology (Rep.trivial ℤ G ℤ) (-2)) :
    tateTwoExtensionMap M (m • c) (-2) x = m • tateTwoExtensionMap M c (-2) x := by
  obtain ⟨g, rfl⟩ := tateScalarGenerator_surjective G x
  rw [tateTwoExtensionMap_generator, tateTwoExtensionMap_generator]
  rw [← map_nsmul (tateInvariantClass M).hom]
  apply congrArg (tateInvariantClass M)
  apply Subtype.ext
  change (∑ h : G, m • c (h, g⁻¹)) = m • ∑ h : G, c (h, g⁻¹)
  exact (Finset.smul_sum ..).symm

/-- The negative cup is additive in the actual ordinary two-class. -/
theorem tateTwoClassMap_negTwo_add (a b : groupCohomology M 2)
    (x : tateCohomology (Rep.trivial ℤ G ℤ) (-2)) :
    tateTwoClassMap M (a + b) (-2) x =
      tateTwoClassMap M a (-2) x + tateTwoClassMap M b (-2) x := by
  obtain ⟨c, rfl⟩ := (ModuleCat.epi_iff_surjective (H2π M)).mp inferInstance a
  obtain ⟨d, rfl⟩ := (ModuleCat.epi_iff_surjective (H2π M)).mp inferInstance b
  rw [← map_add, tateTwoClassMap_class, tateTwoClassMap_class, tateTwoClassMap_class]
  exact tateTwoExtensionMap_negTwo_add M c d x

/-- Natural multiples of the actual ordinary class multiply the negative cup. -/
theorem tateTwoClassMap_negTwo_nsmul (m : ℕ) (a : groupCohomology M 2)
    (x : tateCohomology (Rep.trivial ℤ G ℤ) (-2)) :
    tateTwoClassMap M (m • a) (-2) x = m • tateTwoClassMap M a (-2) x := by
  obtain ⟨c, rfl⟩ := (ModuleCat.epi_iff_surjective (H2π M)).mp inferInstance a
  rw [← map_nsmul, tateTwoClassMap_class, tateTwoClassMap_class]
  exact tateTwoExtensionMap_negTwo_nsmul M m c x

end LocalClassFieldTheory
