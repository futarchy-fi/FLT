/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.TatePositiveCocycleClass
public import FLT.LocalClassFieldTheory.TwoExtensionCochainCup

/-!
# The all-degree Tate operation agrees with cochain cups

The computation takes place on the actual Tate complex. In nonnegative degrees
its two connecting maps give the ordinary cup formula. Positive Tate comparison
then identifies the result with the class in the ordinary cochain complex.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace LocalClassFieldTheory

open CategoryTheory groupCohomology

variable {k G : Type} [CommRing k] [Group G] [Fintype G]

/-- Lifting ordinary cochains also computes the nonnegative Tate boundary. -/
theorem tateConnecting_cochain {S : ShortComplex (Rep k G)} (hS : S.ShortExact) (n : ℕ)
    (z : (Fin n → G) → S.X₃) (hz : inhomogeneousCochains.d S.X₃ n z = 0)
    (y : (Fin n → G) → S.X₂) (hy : S.g.hom ∘ y = z)
    (x : (Fin (n + 1) → G) → S.X₁)
    (hx : S.f.hom ∘ x = (inhomogeneousCochains S.X₂).d n (n + 1) y)
    (hcx : inhomogeneousCochains.d S.X₁ (n + 1) x = 0) :
    TateCohomology.δ hS n (tateClassOfCochain S.X₃ n z hz) =
      tateClassOfCochain S.X₁ (n + 1) x hcx := by
  exact tateConnecting_apply hS n z (by
    rw [tateComplex_d_ofNat, inhomogeneousCochains.d_def]
    exact hz) y hy x hx

variable (M : Rep k G) (c : cocycles₂ M) {n : ℕ} (z : (Fin n → G) → k)
  (hz : inhomogeneousCochains.d (Rep.trivial k G k) n z = 0)

/-- On nonnegative cochains, the actual Tate two-extension map is the ordinary cup. -/
theorem tateTwoExtensionMap_cup :
    tateTwoExtensionMap M c n (tateClassOfCochain (Rep.trivial k G k) n z hz) =
      tateClassOfCochain M (n + 2) (scalarCupTwo M c z) (scalarCupTwo_cycle M c z hz) := by
  have h₁ := tateConnecting_cochain
    (oneCocycleSequence_shortExact _ (shiftedTwoCocycle M c)) n z hz (fun v => (0, z v))
    rfl (scalarCupOne _ (shiftedTwoCocycle M c) z)
    (oneCocycle_scalarLift_d _ (shiftedTwoCocycle M c) z hz)
    (scalarCupOne_cycle _ (shiftedTwoCocycle M c) z hz)
  have h₂ := tateConnecting_cochain (coinducedCoefficientSequence_shortExact M) (n + 1)
    (scalarCupOne _ (shiftedTwoCocycle M c) z)
    (scalarCupOne_cycle _ (shiftedTwoCocycle M c) z hz)
    (scalarCupOne (coinducedCoefficients M) (twoCocyclePrimitive M c) z)
    (by funext v; exact (shiftedProjection M).hom.toLinearMap.map_smul _ _)
    (scalarCupTwo M c z) (twoCocycle_scalarLift_d M c z hz) (scalarCupTwo_cycle M c z hz)
  exact (congrArg (TateCohomology.δ (coinducedCoefficientSequence_shortExact M)
    (n + 1 : ℕ)) h₁).trans h₂

/-- Positive Tate comparison sends the output to the explicit ordinary cup class. -/
theorem tateTwoExtensionMap_positive_cup :
    ((TateCohomology.isoGroupCohomology (n + 2)).app M).hom
      (tateTwoExtensionMap M c n (tateClassOfCochain (Rep.trivial k G k) n z hz)) =
      π M (n + 2) (cocyclesMk (scalarCupTwo M c z) (scalarCupTwo_cycle M c z hz)) := by
  rw [tateTwoExtensionMap_cup, tateClassOfCochain_positive]

end LocalClassFieldTheory
