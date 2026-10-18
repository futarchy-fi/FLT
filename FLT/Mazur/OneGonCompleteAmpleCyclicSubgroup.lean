/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OneGonCompleteFiniteSubgroup
public import FLT.Mazur.OneGonFaithfulCyclicAmple
public import FLT.Mazur.ProperAmpleConverse

/-!
# The actual complete one-gon subgroup is ample and cyclic

The full Cartier generator and the proved relative ampleness of the original
whole subgroup divisor discharge the intrinsic generalized-curve predicates.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory MonObj
namespace FLT.Mazur.OneGonSmoothing
open FCurve GeneralizedEllipticCurve
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (K : Type) [Field K] (n : ℕ) [NeZero n]
  (labels : Multiplicative (ZMod n) →*
    (𝟙_ (Over (Spec (.of K))) ⟶ MultiplicativeGroupScheme.gm K))
  (hlabels : Function.Injective labels)
local notation "H" => completeFiniteSubgroup K n labels hlabels

/-- The original complete subgroup is cyclic in the fppf-local Cartier sense. -/
theorem completeFiniteSubgroup_isCyclic : (H).IsCyclic :=
  (completeFiniteGenerator_isCartierGenerator K n labels hlabels).isCyclic _

/-- The entire original subgroup divisor is ample on the actual generalized curve. -/
theorem completeFiniteSubgroup_isAmple : (H).IsAmple := by
  let _ := family_proper (PowerSeries.X : PowerSeries K)
  unfold FiniteSubgroup.IsAmple
  rw [completeFiniteSubgroup_ideal]
  exact ⟨(faithfulCompleteIdeal_cartier K n labels hlabels).1,
    (faithfulCompleteCyclicLine_relativelyAmple K n labels hlabels).relativeAmple⟩

/-- The specified rank remains the actual subgroup rank at every complete-base point. -/
theorem completeFiniteSubgroup_finrank (s : Spec (.of (PowerSeries K))) :
    (H).carrier.hom.finrank s = n := (H).finrank s

/-- The positive-rank lifted subgroup covers the entire complete coefficient base. -/
theorem completeFiniteSubgroup_surjective : Surjective (H).carrier.hom :=
  (H).surjective (Nat.pos_of_ne_zero (NeZero.ne n))

end FLT.Mazur.OneGonSmoothing
