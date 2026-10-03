/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.TateZeroGroupEquivalence
public import FLT.LocalClassFieldTheory.TwoExtensionCorestriction

/-!
# Transport of the negative fundamental cup

The explicit cocycle-sum formula proves naturality under a group equivalence
and a coefficient morphism, on the actual Tate groups and ordinary two-classes.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace LocalClassFieldTheory

open CategoryTheory groupCohomology

variable {G H : Type} [Group G] [Group H] [Fintype G] [Fintype H]
  (M : Rep ℤ G) (N : Rep ℤ H) (e : H ≃* G) (f : Rep.res e.toMonoidHom M ⟶ N)

/-- Reindexing the invariant cocycle sum commutes with coefficient transport. -/
theorem twoCocycleSumInvariant_groupEquivalence (c : cocycles₂ M) (h : H) :
    groupEquivalenceInvariant M N e f (twoCocycleSumInvariant M c (e h)) =
      twoCocycleSumInvariant N (mapCocycles₂ e.toMonoidHom f c) h := by
  apply Subtype.ext
  change f.hom (∑ g : G, c (g, e h)) = ∑ t : H, f.hom (c (e t, e h))
  rw [map_sum]
  exact (e.toEquiv.sum_comp (fun g => f.hom (c (g, e h)))).symm

/-- The actual negative cup commutes with group equivalence and coefficient transport. -/
theorem tateTwoExtensionMap_groupEquivalence (c : cocycles₂ M)
    (x : tateCohomology (Rep.trivial ℤ H ℤ) (-2)) :
    tateZeroGroupEquivalence M N e f
      (tateTwoExtensionMap M c (-2) (tateScalarMap e.toMonoidHom x)) =
        tateTwoExtensionMap N (mapCocycles₂ e.toMonoidHom f c) (-2) x := by
  obtain ⟨h, rfl⟩ := tateScalarGenerator_surjective H x
  rw [tateScalarMap_generator, tateTwoExtensionMap_generator,
    tateTwoExtensionMap_generator, tateZeroGroupEquivalence_class, ← map_inv]
  exact congrArg (tateInvariantClass N)
    (twoCocycleSumInvariant_groupEquivalence M N e f c h⁻¹)

/-- The group-equivalence cup square depends only on the ordinary two-class. -/
theorem tateTwoClassMap_groupEquivalence (a : groupCohomology M 2)
    (x : tateCohomology (Rep.trivial ℤ H ℤ) (-2)) :
    tateZeroGroupEquivalence M N e f
      (tateTwoClassMap M a (-2) (tateScalarMap e.toMonoidHom x)) =
        tateTwoClassMap N (groupCohomology.map e.toMonoidHom f 2 a) (-2) x := by
  let c := twoClassRepresentative M a
  have hc : H2π M c = a := twoClassRepresentative_spec M a
  rw [← hc]
  have hr := congrArg (fun q => q.hom c) (H2π_comp_map e.toMonoidHom f)
  change groupCohomology.map e.toMonoidHom f 2 (H2π M c) =
    H2π N (mapCocycles₂ e.toMonoidHom f c) at hr
  rw [hr, tateTwoClassMap_class, tateTwoClassMap_class]
  exact tateTwoExtensionMap_groupEquivalence M N e f c x

end LocalClassFieldTheory
