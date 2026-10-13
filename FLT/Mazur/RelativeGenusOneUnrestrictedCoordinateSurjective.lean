/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ProperAmpleDivisorExhaustion
public import FLT.Mazur.RelativeGenusOneUnrestrictedCoordinateImage
public import FLT.Mazur.RelativePointLineAmple

/-!
# Surjectivity onto the full original complement ring

The new ample divisor exhaustion supplies actual tensor numerators over an
arbitrary affine base. Finite-pole generation reaches each such numerator.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Scheme.Modules MonoidalCategory
namespace FLT.Mazur.FCurve.UnrestrictedPole
open ModuleLineBundleTensorPullback
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] divisorLineBundle sectionPoleMultiplicativeCoordinates
  relativePoleFunction

variable {S : Scheme} [IsAffine S]
  (G : Over S) [GrpObj G] [IsProper G.hom]
  [SmoothOfRelativeDimension 1 G.hom] [GeometricallyIntegral G.hom]
  (hg : CurveFiberHypotheses.NodalGenusOneGeometricFibers G.hom)
  (s : 𝟙_ (Over S) ⟶ G) (hI : EffectiveCartier s.left.ker)
  (e : (pullback s.left).obj (divisorLineBundle s.left.ker hI) ≅ structureModule S)

local notation "E" => relativePointCoordinateEvaluation G hg s hI e
local notation "φ" => relativePointComplementBaseMap G s
local notation "W" => relativePointWeierstrassCurve G hg s hI e

/-- The actual cubic evaluation reaches every original complement function. -/
theorem relativePointCoordinateEvaluation_surjective : Function.Surjective E := by
  intro z
  obtain ⟨m, t, ht⟩ := exists_ampleDivisorComplementFunction_unrestricted G.hom hI
    (relative_pointLine_ample G s hI) z
  have h := relativePointCoordinateRange_pole G hg s hI e m ((moduleH0Equiv _).symm t)
  unfold relativePoleFunction at h
  rw [LinearEquiv.apply_symm_apply, ht] at h
  exact h

end FLT.Mazur.FCurve.UnrestrictedPole
