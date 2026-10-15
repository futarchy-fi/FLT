/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteIdentityFirstGraphScheme
public import FLT.Mazur.PolygonCompleteIdentityFirstGraphConductor
public import Mathlib.RingTheory.Localization.Away.Basic

/-!
# The finite original graph is unchanged on both punctured node charts

The uniform conductor powers make the actual source map an isomorphism
after inverting either original node coordinate. Both localization maps
are the maps induced by the constructed source, retaining its nilpotents.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
namespace FLT.Mazur.PolygonInfinitesimalStages
open PolygonSmoothing
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] PolygonSmoothing.relationIdeal
  completeIdentityFirstActionUnit completeIdentityFirstActionField
  completeIdentityFirstActionNodeDefect completeIdentityFirstErrorAlgebra
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n] (i : Fin n)
local notation "R" => K[T;T⁻¹]
local notation "S" => Ring (R) 1
local notation "e" => parameter (R) 1
local notation "B" => ChartRing (e)
local notation "β" => firstNodeBranchPair (R)
local notation "C" => firstNodeBranchSubalgebra (R)
local notation "G" => completeIdentityFirstGraphAlgebra K n h i
local notation "E" => completeIdentityFirstErrorAlgebra K n h i
local notation "f" => AlgHom.toRingHom (completeIdentityFirstGraphSource K n h i)

/-- The constructed source map embeds the entire original nonreduced node ring. -/
theorem completeIdentityFirstGraphSource_injective : Function.Injective (f) := by
  intro a b hab
  apply firstNodeBranchPair_injective (R)
  exact congrArg Subtype.val hab

/-- Any uniform power conductor makes the actual localized source map bijective. -/
theorem completeIdentityFirstGraphSource_localized (w : B)
    (hw : ∃ m : ℕ, 0 < m ∧ ∀ z ∈ (G), z * (β) (w ^ m) ∈ (C)) :
    Function.Bijective (Localization.awayMap (f) w) := by
  constructor
  · apply Localization.awayMap_injective_iff.mpr
    intro a ha
    have hz : a = 0 := completeIdentityFirstGraphSource_injective K n h i
      (ha.trans (map_zero (f)).symm)
    exact ⟨0, by rw [hz, mul_zero]⟩
  · apply Localization.awayMap_surjective_iff.mpr
    intro z
    obtain ⟨m, _, hm⟩ := hw
    have hz : z.val ∈ (G) := by
      rw [← completeIdentityFirstErrorAlgebra_eq_graph]
      exact z.property
    obtain ⟨b, hb⟩ := hm z.val hz
    change (β) b = z.val * (β) (w ^ m) at hb
    refine ⟨b, m, ?_⟩
    apply Subtype.ext
    change (β) b = (β) w ^ m * z.val
    rw [hb, map_pow, mul_comm]

/-- On the left punctured original chart the source is exactly a ring isomorphism. -/
def completeIdentityFirstGraphLeftEquiv :
    Localization.Away (leftCoordinate (e)) ≃+*
      Localization.Away ((f) (leftCoordinate (e))) := by
  let _ : CommRing (E) := inferInstance
  exact RingEquiv.ofBijective (Localization.awayMap (f) (leftCoordinate (e)))
    (completeIdentityFirstGraphSource_localized K n h i _
      (completeIdentityFirstGraphAlgebra_left_conductor K n h i))

/-- On the right punctured original chart the same source map is also an isomorphism. -/
def completeIdentityFirstGraphRightEquiv :
    Localization.Away (rightCoordinate (e)) ≃+*
      Localization.Away ((f) (rightCoordinate (e))) := by
  let _ : CommRing (E) := inferInstance
  exact RingEquiv.ofBijective (Localization.awayMap (f) (rightCoordinate (e)))
    (completeIdentityFirstGraphSource_localized K n h i _
      (completeIdentityFirstGraphAlgebra_right_conductor K n h i))

/-- The left isomorphism is the actual localization of the original graph source map. -/
theorem completeIdentityFirstGraphLeftEquiv_toRingHom :
    (completeIdentityFirstGraphLeftEquiv K n h i).toRingHom =
      Localization.awayMap (f) (leftCoordinate (e)) := rfl

/-- The right isomorphism likewise retains the original source on every localized element. -/
theorem completeIdentityFirstGraphRightEquiv_toRingHom :
    (completeIdentityFirstGraphRightEquiv K n h i).toRingHom =
      Localization.awayMap (f) (rightCoordinate (e)) := rfl

end FLT.Mazur.PolygonInfinitesimalStages
