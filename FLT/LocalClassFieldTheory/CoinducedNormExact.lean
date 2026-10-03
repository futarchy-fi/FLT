/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.CoinducedCoefficientSequence

/-!
# Exactness at the coinduced norm splice

Point masses give explicit preimages under the norm and the augmentation
differential, including for coefficients with torsion.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace LocalClassFieldTheory

open CategoryTheory groupCohomology groupHomology

variable {k G : Type} [CommRing k] [Group G] [Fintype G] (M : Rep k G)

/-- The norm of a function is the constant function with value its sum. -/
theorem coinducedNorm_apply (f : coinducedCoefficients M) (x : G) :
    (coinducedCoefficients M).norm.hom f x = ∑ g : G, f g := by
  change ((∑ g : G, (coinducedCoefficients M).ρ g) f) x = _
  rw [LinearMap.sum_apply, Finset.sum_apply]
  change (∑ g : G, f (x * g)) = _
  exact Fintype.sum_equiv (Equiv.mulLeft x) _ _ (fun _ => rfl)

/-- Every invariant coinduced function is a norm. -/
theorem coinducedNorm_surjective_on_invariants (f : coinducedCoefficients M)
    (hf : d₀₁ (coinducedCoefficients M) f = 0) :
    ∃ b, (coinducedCoefficients M).norm.hom b = f := by
  classical
  refine ⟨Pi.single 1 (f 1), ?_⟩
  funext x
  rw [coinducedNorm_apply]
  have h := congrFun (congrFun hf x) 1
  change f (1 * x) - f 1 = 0 at h
  simpa using (sub_eq_zero.mp h).symm

/-- An explicit chain whose boundary removes the sum of a function at the identity. -/
theorem coinduced_augmentation_boundary [DecidableEq G] (f : coinducedCoefficients M) :
    d₁₀ (coinducedCoefficients M)
      (∑ g : G, Finsupp.single g (Pi.single 1 (f g))) =
        (fun x => f x - Pi.single (M := fun _ : G => M) 1 (∑ g : G, f g) x) := by
  classical
  funext x
  rw [map_sum]
  change (∑ g : G, (d₁₀ (coinducedCoefficients M)
    (Finsupp.single g (Pi.single 1 (f g))) : G → M)) x = _
  rw [Finset.sum_apply]
  simp only [d₁₀_single (coinducedCoefficients M)]
  change (∑ g : G, (Pi.single (M := fun _ : G => M) 1 (f g) (x * g⁻¹) -
    Pi.single (M := fun _ : G => M) 1 (f g) x)) = _
  simp only [Finset.sum_sub_distrib, Pi.single_apply, mul_inv_eq_one]
  simp

/-- Every norm-zero coinduced function is an augmentation boundary. -/
theorem coinducedNorm_kernel (f : coinducedCoefficients M)
    (hf : (coinducedCoefficients M).norm.hom f = 0) :
    ∃ b, d₁₀ (coinducedCoefficients M) b = f := by
  classical
  have hs : ∑ g : G, f g = 0 := by
    exact (coinducedNorm_apply M f 1).symm.trans (congrFun hf 1)
  refine ⟨∑ g : G, Finsupp.single g (Pi.single 1 (f g)), ?_⟩
  rw [coinduced_augmentation_boundary, hs]
  simp

end LocalClassFieldTheory
