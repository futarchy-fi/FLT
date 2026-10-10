/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.IdealAdicClosedAmpleSerreBound
public import FLT.Mazur.IdealAdicUniformGradedVanishing
public import FLT.Mazur.IdealAdicCohomology

/-!
# Uniform infinitesimal vanishing from closed-source ampleness

One twist bound kills positive cohomology in every actual graded piece and
finite quotient. Only the restriction of the line to the closed source is
assumed ample, as needed in the fiber-to-neighborhood construction.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open Scheme.Modules FLT.Mazur.FCurve FLT.Mazur.IdealAdicQuotient
open ModuleSheafTensor ModuleLineBundleTensorPullback

namespace FLT.Mazur.IdealAdicGradedPullback

variable {X Y : Scheme.{0}} [IsLocallyNoetherian X] [IsLocallyNoetherian Y] [IsAffine Y]
  (J : Y.IdealSheafData) (f : X ⟶ Y) [IsProper f] {L : X.Modules}
  (hline : LocallyFreeRankOne L)
  (hL : AmpleLineBundle ((pullback (J.comap f).subschemeι).obj L))

include hline hL

/-- The homogeneous retractions give one bound from ampleness only on the closed source. -/
theorem idealGraded_uniform_serreBound_of_closed :
    ∃ N : ℕ, ∀ m ≥ N, ∀ n q : ℕ,
      Subsingleton (ModuleH (tensor (idealGraded (J.comap f) n) (tensorPower L m)) (q + 1)) := by
  obtain ⟨N, hN⟩ := relativeDescendedPushforward_serreBound_of_closed J f hline hL
  refine ⟨N, fun m hm n q ↦ ?_⟩
  exact moduleH_subsingleton_of_split
    (ModuleSheafTensor.map (relativeHomogeneousInclusion J f n) (𝟙 (tensorPower L m)))
    (ModuleSheafTensor.map (relativeHomogeneousProjection J f n) (𝟙 (tensorPower L m)))
    (relativeHomogeneousTwist_retraction J f n (tensorPower L m)) (q + 1) (hN m hm q)

/-- The same closed-source bound applies to every original line-power graded coefficient. -/
theorem gradedLine_uniform_serreBound_of_closed :
    ∃ N : ℕ, ∀ m ≥ N, ∀ n q : ℕ,
      let _ := (hline.tensorPower m).isFinitePresentation
      Subsingleton (ModuleH (graded (J.comap f) (tensorPower L m) n) (q + 1)) := by
  obtain ⟨N, hN⟩ := idealGraded_uniform_serreBound_of_closed J f hline hL
  refine ⟨N, fun m hm n q ↦ ?_⟩
  let _ := (hline.tensorPower m).isFinitePresentation
  exact @moduleH_subsingleton_of_iso X _ _
    (gradedLineTwistIso (J.comap f) (tensorPower L m) (hline.tensorPower m) n) (q + 1)
    (hN m hm n q)

/-- Every finite quotient has vanishing positive cohomology above the same line-twist bound. -/
theorem quotientLine_uniform_serreBound_of_closed :
    ∃ N : ℕ, ∀ m ≥ N, ∀ n q : ℕ,
      let _ := (hline.tensorPower m).isFinitePresentation
      Subsingleton (ModuleH (quotient (J.comap f) (tensorPower L m) n) (q + 1)) := by
  obtain ⟨N, hN⟩ := gradedLine_uniform_serreBound_of_closed J f hline hL
  refine ⟨N, fun m hm n q ↦ ?_⟩
  let _ := (hline.tensorPower m).isFinitePresentation
  exact quotient_moduleH_subsingleton (J.comap f) (tensorPower L m) (q + 1)
    (fun k ↦ hN m hm k q) n

/-- The closed-source bound also makes all actual finite H0 reductions surjective. -/
theorem reductionLine_h0_uniform_surjective_of_closed :
    ∃ N : ℕ, ∀ m ≥ N, ∀ a b : ℕ, ∀ hab : a ≤ b,
      let _ := (hline.tensorPower m).isFinitePresentation
      Function.Surjective (moduleHMap (reduction (J.comap f) (tensorPower L m) hab) 0) := by
  obtain ⟨N, hN⟩ := gradedLine_uniform_serreBound_of_closed J f hline hL
  refine ⟨N, fun m hm a b hab ↦ ?_⟩
  let _ := (hline.tensorPower m).isFinitePresentation
  exact reduction_h0_surjective_of_le (J.comap f) (tensorPower L m)
    (fun k ↦ hN m hm k 0) hab

end FLT.Mazur.IdealAdicGradedPullback
