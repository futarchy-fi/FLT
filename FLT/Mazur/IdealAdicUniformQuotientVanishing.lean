/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.IdealAdicUniformGradedVanishing
public import FLT.Mazur.IdealAdicCohomology

/-!
# Uniform vanishing and H0 reduction on actual infinitesimal quotients

The uniform graded bound gives one line-twist bound for every quotient
thickening and every positive cohomological degree. The same bound makes
all finite H0 reductions surjective, including reduction to the closed fibre.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open FLT.Mazur.FCurve FLT.Mazur.IdealAdicQuotient
open ModuleLineBundleTensorPullback

namespace FLT.Mazur.IdealAdicGradedPullback

variable {X Y : Scheme.{0}} [IsLocallyNoetherian X] [IsLocallyNoetherian Y] [IsAffine Y]
variable (J : Y.IdealSheafData) (f : X ⟶ Y) [IsProper f]

/-- One twist bound kills positive cohomology on every actual infinitesimal quotient. -/
theorem quotientLine_uniform_serreBound {L : X.Modules} (hL : AmpleLineBundle L) :
    ∃ N : ℕ, ∀ m ≥ N, ∀ n q : ℕ,
      let _ := (hL.2.1.tensorPower m).isFinitePresentation
      Subsingleton (ModuleH (quotient (J.comap f) (tensorPower L m) n) (q + 1)) := by
  obtain ⟨N, hN⟩ := gradedLine_uniform_serreBound J f hL
  refine ⟨N, fun m hm n q ↦ ?_⟩
  let _ := (hL.2.1.tensorPower m).isFinitePresentation
  exact quotient_moduleH_subsingleton (J.comap f) (tensorPower L m) (q + 1)
    (fun k ↦ hN m hm k q) n

/-- One twist bound makes all actual finite-thickening H0 reductions surjective. -/
theorem reductionLine_h0_uniform_surjective {L : X.Modules} (hL : AmpleLineBundle L) :
    ∃ N : ℕ, ∀ m ≥ N, ∀ a b : ℕ, ∀ hab : a ≤ b,
      let _ := (hL.2.1.tensorPower m).isFinitePresentation
      Function.Surjective (moduleHMap (reduction (J.comap f) (tensorPower L m) hab) 0) := by
  obtain ⟨N, hN⟩ := gradedLine_uniform_serreBound J f hL
  refine ⟨N, fun m hm a b hab ↦ ?_⟩
  let _ := (hL.2.1.tensorPower m).isFinitePresentation
  exact reduction_h0_surjective_of_le (J.comap f) (tensorPower L m)
    (fun k ↦ hN m hm k 0) hab

/-- Reduction of actual global sections across any finite pair of thickenings is surjective. -/
theorem reductionLine_sections_uniform_surjective {L : X.Modules} (hL : AmpleLineBundle L) :
    ∃ N : ℕ, ∀ m ≥ N, ∀ a b : ℕ, ∀ hab : a ≤ b,
      let _ := (hL.2.1.tensorPower m).isFinitePresentation
      Function.Surjective ((reduction (J.comap f) (tensorPower L m) hab).app ⊤) := by
  obtain ⟨N, hN⟩ := reductionLine_h0_uniform_surjective J f hL
  refine ⟨N, fun m hm a b hab ↦ ?_⟩
  let _ := (hL.2.1.tensorPower m).isFinitePresentation
  refine fun s ↦ ?_
  obtain ⟨t, ht⟩ := hN m hm a b hab
    ((moduleH0Equiv (quotient (J.comap f) (tensorPower L m) a)).symm s)
  refine ⟨moduleH0Equiv (quotient (J.comap f) (tensorPower L m) b) t, ?_⟩
  rw [← moduleH0Equiv_naturality, ht]
  exact (moduleH0Equiv (quotient (J.comap f) (tensorPower L m) a)).apply_symm_apply s

end FLT.Mazur.IdealAdicGradedPullback
