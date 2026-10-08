/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.IdealAdicRelativeSerreBound
public import FLT.Mazur.AffinePushforwardCohomology

/-!
# A Serre bound for twists of the actual descended pushforward

The line projection formula and affine cohomology comparison carry the
changed-base Serre bound to the original source. This is one bound for the
whole actual pushforward; extracting its homogeneous summands is separate.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Scheme.Modules FLT.Mazur.FCurve
open ModuleSheafTensor ModuleLineBundleTensorPullback

namespace FLT.Mazur.IdealAdicGradedPullback

variable {X Y : Scheme.{0}} [IsLocallyNoetherian X] [IsLocallyNoetherian Y] [IsAffine Y]
variable (J : Y.IdealSheafData) (f : X ⟶ Y)

/-- Projection of the actual changed-base twist is the twist of its actual pushforward. -/
def relativeDescendedPushforwardTwistIso {L : X.Modules} (hL : LocallyFreeRankOne L)
    (n : ℕ) :
    (pushforward (relativeSchemeToSource J f)).obj
        (tensor (relativeDescendedCoefficientSheaf J f)
          (tensorPower (relativeCoefficientLine J f L) n)) ≅
      tensor (relativeDescendedCoefficientPushforward J f) (tensorPower L n) :=
  (pushforward (relativeSchemeToSource J f)).mapIso
    (ModuleSheafTensor.congr (Iso.refl _)
      (tensorPowerIso (relativeSchemeToSource J f) L n).symm) ≪≫
    ClosedLineProjectionFormula.projectionIso (relativeSchemeToSource J f)
      (relativeDescendedCoefficientSheaf J f) (tensorPower L n) (hL.tensorPower n)

/-- A single bound kills every positive cohomology of all large pushforward twists. -/
theorem relativeDescendedPushforward_serreBound [IsProper f]
    {L : X.Modules} (hL : AmpleLineBundle L) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ q : ℕ,
      Subsingleton (ModuleH
        (tensor (relativeDescendedCoefficientPushforward J f) (tensorPower L n)) (q + 1)) := by
  let _ : X.IsSeparated := ⟨by rw [← terminal.comp_from f]; infer_instance⟩
  obtain ⟨N, hN⟩ := relativeDescendedCoefficient_serreBound J f hL
  refine ⟨N, fun n hn q ↦ ?_⟩
  let M := tensor (relativeDescendedCoefficientSheaf J f)
    (tensorPower (relativeCoefficientLine J f L) n)
  let _ := tensor_line_isFinitePresentation (relativeDescendedCoefficientSheaf J f)
    (tensorPower (relativeCoefficientLine J f L) n)
    ((relativeCoefficientLine_ample J f hL).2.1.tensorPower n)
  have h := (affinePushforward_moduleH_subsingleton_iff
    (relativeSchemeToSource J f) M (q + 1)).mpr (hN n hn q)
  exact @moduleH_subsingleton_of_iso X _ _
    (relativeDescendedPushforwardTwistIso J f hL.2.1 n).symm (q + 1) h

end FLT.Mazur.IdealAdicGradedPullback
