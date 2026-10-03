/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.TateScalarMap
public import FLT.LocalClassFieldTheory.TateZeroTransfer
public import FLT.LocalClassFieldTheory.TateTwoClassOperation
public import FLT.LocalClassFieldTheory.TwoExtensionNegativeEvaluation

/-!
# The degree-minus-two cup and subgroup corestriction

The diagram commutes on the constructed maps. The proof computes both
boundaries on scalar generators and uses the cocycle-sum norm identity.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace LocalClassFieldTheory

open CategoryTheory groupCohomology

variable {G : Type} [Group G] [Fintype G]
  (M : Rep ℤ G) (H : Subgroup G) [Fintype H] [Fintype (G ⧸ H)]

local notation "MH" => Rep.res H.subtype M

/-- The actual two-extension cup commutes with subgroup corestriction in degree minus two. -/
theorem tateTwoExtensionMap_corestriction (c : cocycles₂ M)
    (x : tateCohomology (Rep.trivial ℤ H ℤ) (-2)) :
    tateZeroCorestriction M H
      (tateTwoExtensionMap MH (mapCocycles₂ H.subtype (𝟙 MH) c) (-2) x) =
        tateTwoExtensionMap M c (-2) (tateScalarMap H.subtype x) := by
  obtain ⟨g, rfl⟩ := tateScalarGenerator_surjective H x
  rw [tateScalarMap_generator, tateTwoExtensionMap_generator,
    tateTwoExtensionMap_generator, tateZeroCorestriction_class]
  apply congrArg (tateInvariantClass M)
  apply Subtype.ext
  exact twoCocycleSum_transfer M c H g⁻¹

/-- The corestriction diagram depends only on the ordinary two-class. -/
theorem tateTwoClassMap_corestriction (a : groupCohomology M 2)
    (x : tateCohomology (Rep.trivial ℤ H ℤ) (-2)) :
    tateZeroCorestriction M H
      (tateTwoClassMap MH (groupCohomology.map H.subtype (𝟙 MH) 2 a) (-2) x) =
        tateTwoClassMap M a (-2) (tateScalarMap H.subtype x) := by
  let c := twoClassRepresentative M a
  have hc : H2π M c = a := twoClassRepresentative_spec M a
  rw [← hc]
  have hr := congrArg (fun f => f.hom c) (H2π_comp_map H.subtype (𝟙 MH))
  change groupCohomology.map H.subtype (𝟙 MH) 2 (H2π M c) =
    H2π MH (mapCocycles₂ H.subtype (𝟙 MH) c) at hr
  rw [hr, tateTwoClassMap_class, tateTwoClassMap_class]
  exact tateTwoExtensionMap_corestriction M H c x

end LocalClassFieldTheory
