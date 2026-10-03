/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.FiniteHomSum
public import FLT.LocalClassFieldTheory.TwoCocycleNormSum

/-!
# The cocycle sum of an inflated two-class

Pullback along a surjection repeats each summand once per kernel element.
This is the multiplicity in the negative-cup inflation comparison.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace LocalClassFieldTheory

open CategoryTheory groupCohomology

variable {k G H : Type} [CommRing k] [Group G] [Group H] [Fintype G] [Fintype H]
  (M : Rep k H) (P : Rep k G) (f : G →* H) (φ : Rep.res f M ⟶ P)

/-- Coefficient transport sends full invariants to full invariants after pullback. -/
def inflationInvariant : M.ρ.invariants →ₗ[k] P.ρ.invariants where
  toFun x := ⟨φ.hom x, fun g => by
    rw [← Rep.hom_comm_apply]
    exact congrArg φ.hom (x.property (f g))⟩
  map_add' x y := Subtype.ext (map_add φ.hom x.val y.val)
  map_smul' r x := Subtype.ext (map_smul φ.hom r x.val)

/-- The invariant cocycle sum of a pullback retains its kernel multiplicity. -/
theorem twoCocycleSumInvariant_inflation (hf : Function.Surjective f)
    (c : cocycles₂ M) (g : G) :
    twoCocycleSumInvariant P (mapCocycles₂ f φ c) g =
      Nat.card f.ker • inflationInvariant M P f φ (twoCocycleSumInvariant M c (f g)) := by
  apply Subtype.ext
  change (∑ t : G, φ.hom (c (f t, f g))) =
    Nat.card f.ker • φ.hom (∑ h : H, c (h, f g))
  rw [sum_surjective_hom f hf (fun h => φ.hom (c (h, f g))), map_sum]

end LocalClassFieldTheory
