/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.IdealAdicRelativeDescendedScalars
public import FLT.Mazur.AmpleAffinePullback
public import FLT.Mazur.AmpleCoherentVanishing

/-!
# A Serre bound on the actual changed-base coefficient module

The affine projection preserves ampleness and the coefficient module
constructed by descent is coherent. Apply Serre vanishing over the actual
Noetherian graded base to this one module, before taking coefficient degrees.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry
open Scheme.Modules FLT.Mazur.FCurve
open ModuleSheafTensor ModuleLineBundleTensorPullback
open FLT.Mazur.IdealAdicGradedSections

namespace FLT.Mazur.IdealAdicGradedPullback

variable {X Y : Scheme.{0}} [IsLocallyNoetherian X] [IsLocallyNoetherian Y] [IsAffine Y]
variable (J : Y.IdealSheafData) (f : X ⟶ Y)

/-- The original line bundle pulled to the actual changed-base coefficient scheme. -/
def relativeCoefficientLine (L : X.Modules) : (relativeScheme J f).Modules :=
  (pullback (relativeSchemeToSource J f)).obj L

omit [IsLocallyNoetherian X] [IsAffine Y] in
/-- The actual affine projection preserves the given ample line bundle. -/
lemma relativeCoefficientLine_ample {L : X.Modules} (hL : AmpleLineBundle L) :
    AmpleLineBundle (relativeCoefficientLine J f L) :=
  hL.pullback_affine (relativeSchemeToSource J f)

attribute [local irreducible] relativeDescendedCoefficientSheaf relativeCoefficientLine
attribute [local irreducible] relativeScheme relativeSchemeToBase

/-- One Serre bound annihilates all positive cohomology of the entire descended module. -/
theorem relativeDescendedCoefficient_serreBound [IsProper f]
    {L : X.Modules} (hL : AmpleLineBundle L) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ q : ℕ,
      Subsingleton (ModuleH (tensor (relativeDescendedCoefficientSheaf J f)
        (tensorPower (relativeCoefficientLine J f L) n)) (q + 1)) := by
  let _ := affineSections_isNoetherianRing J ⟨⊤, isAffineOpen_top Y⟩
  exact AmpleLineBundle.coherent_vanishing
    (R := IdealAdicGradedSections.Sections J ⊤) (relativeSchemeToBase J f)
    (relativeCoefficientLine_ample J f hL) (relativeDescendedCoefficientSheaf J f)

end FLT.Mazur.IdealAdicGradedPullback
