/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.PadicHodgeTheory.ComplexCyclotomicGalois
public import FLT.PadicHodgeTheory.ComplexCyclotomicProjection

/-! # The extended normalized trace is invariant under the relative Galois group -/

@[expose] public noncomputable section
namespace PadicHodgeTheory
variable (p : ℕ) [Fact p.Prime]

/-- Automorphisms over a target level leave the original algebraic trace unchanged. -/
theorem padicCyclotomicProjection_relative_invariant (n : ℕ)
    (σ : Gal(PadicAlgCl p/padicCyclotomicTower p (n + 1))) (x : PadicAlgCl p) :
    padicCyclotomicProjection p (n + 1) (σ x) = padicCyclotomicProjection p (n + 1) x := by
  apply congrArg Subtype.val
  exact Algebra.normalizedTrace_map (padicCyclotomicTower p (n + 1)) (PadicAlgCl p) σ.toAlgHom x

/-- Density extends relative Galois invariance to the actual completed projections. -/
theorem complexCyclotomicProjection_relative_invariant (n : ℕ)
    (σ : Gal(PadicAlgCl p/padicCyclotomicTower p (n + 1))) (x : complexCyclotomicClosure p) :
    complexCyclotomicProjection p n
      (complexCyclotomicGalois p (σ.restrictScalars ℚ_[p]) x) =
        complexCyclotomicProjection p n x := by
  refine (complexCyclotomicInclusion_dense p).induction_on x
    (isClosed_eq ((complexCyclotomicProjection p n).continuous.comp
      (complexCyclotomicGalois p (σ.restrictScalars ℚ_[p])).continuous)
      (complexCyclotomicProjection p n).continuous) ?_
  intro b
  rw [complexCyclotomicGalois_inclusion, complexCyclotomicProjection_inclusion,
    complexCyclotomicProjection_inclusion]
  exact congrArg (fun a : PadicAlgCl p ↦ (a : ℂ_[p]))
    (padicCyclotomicProjection_relative_invariant p n σ b)

end PadicHodgeTheory
