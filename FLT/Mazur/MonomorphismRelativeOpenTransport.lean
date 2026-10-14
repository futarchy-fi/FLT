/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.MonomorphismRelativeOpen
public import FLT.Mazur.MonomorphismOpenImageBaseChange

/-!
# Retaining effective opens across a change of model

Only the square comparing the full relations with their candidate kernels is
required to be Cartesian. The target comparison merely commutes. Thus this
applies to reselected coefficient models without a target base-change premise.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace FLT.Mazur.MonomorphismRelativeOpen
variable {D K T D' K' T' : Scheme.{u}} (m : D ⟶ K) [Mono m] (q : K ⟶ T)
  (a : D' ⟶ D) (m' : D' ⟶ K') (b : K' ⟶ K) (q' : K' ⟶ T') (t : T' ⟶ T)
  (hD : IsPullback a m' m b) (hK : b ≫ q = q' ≫ t)

include hD hK in
/-- Every old effective target neighborhood remains effective in the new model. -/
theorem preimage_targetOpen_le : t ⁻¹ᵁ targetOpen m q ≤ targetOpen m' q' := by
  apply SchemeWholeFiberOpen.le_locus
  intro x hx
  apply MonomorphismOpenImage.preimage_locus_le m a m' b hD
  apply SchemeWholeFiberOpen.preimage_le q (MonomorphismOpenImage.locus m)
  change q (b x) ∈ targetOpen m q
  rw [show q (b x) = t (q' x) from congrArg (fun z ↦ z x) hK]
  exact hx

include hD hK in
/-- Full old effectivity implies full new effectivity, even without a flat target map. -/
theorem targetOpen_top_of_old (he : targetOpen m q = ⊤) : targetOpen m' q' = ⊤ := by
  apply top_le_iff.mp
  have hh := preimage_targetOpen_le m q a m' b q' t hD hK
  rw [he] at hh
  exact hh

end FLT.Mazur.MonomorphismRelativeOpen
