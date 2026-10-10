/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.IdealAdicRelativePushforwardSerreBound

/-!
# Uniform Serre bounds from ampleness on the closed source

The graded coefficient scheme projects affinely to the closed source.
Ampleness only on that closed source therefore suffices for Serre vanishing
on the actual descended graded coefficient, without ampleness on all of X.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Scheme.Modules FLT.Mazur.FCurve
open ModuleSheafTensor ModuleLineBundleTensorPullback
open FLT.Mazur.IdealAdicGradedSections

namespace FLT.Mazur.IdealAdicGradedPullback

variable {X Y : Scheme.{0}} [IsLocallyNoetherian X] [IsLocallyNoetherian Y] [IsAffine Y]
  (J : Y.IdealSheafData) (f : X ⟶ Y) {L : X.Modules}

omit [IsLocallyNoetherian X] [IsAffine Y] in
/-- Closed-source ampleness pulls back to the actual graded coefficient scheme. -/
lemma relativeCoefficientLine_ample_of_closed
    (hL : AmpleLineBundle ((Scheme.Modules.pullback (J.comap f).subschemeι).obj L)) :
    AmpleLineBundle (relativeCoefficientLine J f L) := by
  exact (hL.pullback_affine (relativeSchemeToClosed J f)).of_iso
    ((pullbackComp (relativeSchemeToClosed J f) (J.comap f).subschemeι).app L).symm

attribute [local irreducible] relativeDescendedCoefficientSheaf relativeCoefficientLine
attribute [local irreducible] relativeScheme relativeSchemeToBase

/-- A uniform Serre bound uses only ampleness on the closed source. -/
theorem relativeDescendedCoefficient_serreBound_of_closed [IsProper f]
    (hL : AmpleLineBundle ((Scheme.Modules.pullback (J.comap f).subschemeι).obj L)) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ q : ℕ,
      Subsingleton (ModuleH (tensor (relativeDescendedCoefficientSheaf J f)
        (tensorPower (relativeCoefficientLine J f L) n)) (q + 1)) := by
  let _ := affineSections_isNoetherianRing J ⟨⊤, isAffineOpen_top _⟩
  exact AmpleLineBundle.coherent_vanishing
    (R := IdealAdicGradedSections.Sections J ⊤) (relativeSchemeToBase J f)
    (relativeCoefficientLine_ample_of_closed J f hL) (relativeDescendedCoefficientSheaf J f)

/-- The same bound holds for the actual ambient pushforward twisted by the original line. -/
theorem relativeDescendedPushforward_serreBound_of_closed [IsProper f]
    (hline : LocallyFreeRankOne L)
    (hL : AmpleLineBundle ((Scheme.Modules.pullback (J.comap f).subschemeι).obj L)) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ q : ℕ,
      Subsingleton (ModuleH
        (tensor (relativeDescendedCoefficientPushforward J f) (tensorPower L n)) (q + 1)) := by
  let _ : X.IsSeparated := ⟨by rw [← terminal.comp_from f]; infer_instance⟩
  obtain ⟨N, hN⟩ := relativeDescendedCoefficient_serreBound_of_closed J f hL
  refine ⟨N, fun n hn q ↦ ?_⟩
  let M := tensor (relativeDescendedCoefficientSheaf J f)
    (tensorPower (relativeCoefficientLine J f L) n)
  let _ := tensor_line_isFinitePresentation (relativeDescendedCoefficientSheaf J f)
    (tensorPower (relativeCoefficientLine J f L) n)
    ((relativeCoefficientLine_ample_of_closed J f hL).2.1.tensorPower n)
  have h := (affinePushforward_moduleH_subsingleton_iff
    (relativeSchemeToSource J f) M (q + 1)).mpr (hN n hn q)
  exact @moduleH_subsingleton_of_iso X _ _
    (relativeDescendedPushforwardTwistIso J f hline n).symm (q + 1) h

end FLT.Mazur.IdealAdicGradedPullback
