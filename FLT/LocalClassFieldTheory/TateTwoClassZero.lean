/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.TateTwoClassOperation

/-!
# The zero class acts by zero on Tate cohomology

The zero one-cocycle has a split extension. Its connecting map vanishes in
every integer degree, so the two-extension operation vanishes on boundaries.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace LocalClassFieldTheory

open CategoryTheory Limits groupCohomology

variable {k G : Type} [CommRing k] [Group G] (Q : Rep k G)

/-- The zero extension has an equivariant section of its scalar projection. -/
def zeroCocycleSection : Rep.trivial k G k ⟶ oneCocycleExtension Q 0 :=
  Rep.ofHom ⟨LinearMap.inr k Q k, fun g => by
    apply LinearMap.ext
    intro r
    apply Prod.ext
    · change 0 = Q.ρ g 0 + r • (0 : Q)
      simp
    · rfl⟩

/-- The section is a right inverse to the extension projection. -/
theorem zeroCocycleSection_projection :
    zeroCocycleSection Q ≫ oneCocycleProjection Q 0 = 𝟙 _ := by ext; rfl

variable [Fintype G]

/-- The connecting map of the split extension vanishes even in nonpositive degrees. -/
theorem zeroCocycle_tateConnecting (n : ℤ) :
    TateCohomology.δ (oneCocycleSequence_shortExact Q 0) n = 0 := by
  have h := TateCohomology.map_δ (oneCocycleSequence_shortExact Q 0) n
  have hs := congrArg ((tateCohomologyFunctor n).map) (zeroCocycleSection_projection Q)
  rw [(tateCohomologyFunctor n).map_comp, (tateCohomologyFunctor n).map_id] at hs
  dsimp only [oneCocycleSequence] at h
  calc
    _ = (tateCohomologyFunctor n).map (zeroCocycleSection Q) ≫
        (tateCohomologyFunctor n).map (oneCocycleProjection Q 0) ≫
          TateCohomology.δ (oneCocycleSequence_shortExact Q 0) n := by
            rw [← Category.assoc, hs]
            simp
    _ = 0 := by rw [h, comp_zero]

omit [Fintype G] in
/-- The dimension-shift construction takes the zero two-cocycle to zero. -/
theorem shiftedTwoCocycle_zero (M : Rep k G) : shiftedTwoCocycle M 0 = 0 := by
  apply cocycles₁_ext
  intro g
  exact map_zero (shiftedProjection M).hom

/-- The zero two-cocycle acts by zero in all Tate degrees. -/
theorem tateTwoExtensionMap_zero (M : Rep k G) (n : ℤ) :
    tateTwoExtensionMap M 0 n = 0 := by
  simp only [tateTwoExtensionMap, zeroCocycle_tateConnecting,
    zero_comp]

/-- The zero cohomology class acts by zero in all Tate degrees. -/
theorem tateTwoClassMap_zero (M : Rep k G) (n : ℤ) : tateTwoClassMap M 0 n = 0 := by
  have h := tateTwoClassMap_class M 0 n
  rw [map_zero, tateTwoExtensionMap_zero] at h
  exact h

end LocalClassFieldTheory
