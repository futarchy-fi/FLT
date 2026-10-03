/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.CoinducedCoefficientSequence

/-!
# Dimension shifting a two-cocycle

The function `g ↦ (x ↦ c(x,g))` has coboundary equal to the orbit
embedding of `c`. Its projection is therefore a one-cocycle in the quotient.
The ordinary connecting map recovers the original two-class with positive sign.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace LocalClassFieldTheory

open CategoryTheory groupCohomology

variable {k G : Type} [CommRing k] [Group G] (M : Rep k G) (c : cocycles₂ M)

/-- A concrete primitive of the embedded two-cocycle in coinduced coefficients. -/
def twoCocyclePrimitive (g : G) : coinducedCoefficients M := fun x => c (x, g)

/-- The primitive has exactly the required coboundary, without a sign change. -/
theorem twoCocyclePrimitive_d :
    (coinducedInclusion M).hom ∘ c = d₁₂ (coinducedCoefficients M) (twoCocyclePrimitive M c) := by
  funext z x
  change M.ρ x (c (z.1, z.2)) = c (x * z.1, z.2) - c (x, z.1 * z.2) + c (x, z.1)
  have h := (mem_cocycles₂_iff c).mp c.property x z.1 z.2
  rw [← sub_eq_iff_eq_add] at h
  rw [← h]
  abel

/-- The quotient of the primitive is a one-cocycle. -/
def shiftedTwoCocycle : cocycles₁ (shiftedCoefficients M) :=
  ⟨fun g => (shiftedProjection M).hom (twoCocyclePrimitive M c g), by
    apply (mem_cocycles₁_def _).mpr
    intro g h
    rw [← Rep.hom_comm_apply, ← map_sub, ← map_add]
    have hd := congrFun (twoCocyclePrimitive_d M c) (g, h)
    change (shiftedProjection M).hom ((d₁₂ (coinducedCoefficients M)
      (twoCocyclePrimitive M c)) (g, h)) = 0
    rw [← hd]
    exact (Submodule.Quotient.mk_eq_zero _).mpr ⟨c (g, h), rfl⟩⟩

/-- The genuine connecting map sends the shifted cocycle back to its original class. -/
theorem shiftedTwoCocycle_connecting :
    groupCohomology.δ (coinducedCoefficientSequence_shortExact M) 1 2 rfl
      (H1π (shiftedCoefficients M) (shiftedTwoCocycle M c)) = H2π M c := by
  exact δ₁_apply (coinducedCoefficientSequence_shortExact M)
    (shiftedTwoCocycle M c) (twoCocyclePrimitive M c) rfl c (twoCocyclePrimitive_d M c)

end LocalClassFieldTheory
