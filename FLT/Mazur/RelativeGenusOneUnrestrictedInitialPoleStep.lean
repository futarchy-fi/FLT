/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RelativeGenusOneInitialPoleStep
public import FLT.Mazur.RelativeGenusOneUnrestrictedCanonicalConstants
public import FLT.Mazur.RelativeGenusOneUnrestrictedLowPoleBasis

/-!
# The canonical degree-zero to degree-one pole step

The original divisor inclusion sends the normalized constant basis to the
normalized degree-one basis. This is compatibility of the actual map, not
merely an abstract identification of two free rank-one modules.

The original base is arbitrary; no Noetherian hypothesis is required.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Scheme.Modules MonoidalCategory Module
namespace FLT.Mazur.FCurve.UnrestrictedPole
open ModuleSheafTensor ModuleLineBundleTensorPullback
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] ModuleSheafTensor.tensor divisorLineBundle

variable {S : Scheme}
  (G : Over S) [GrpObj G] [IsProper G.hom]
  [SmoothOfRelativeDimension 1 G.hom] [GeometricallyIntegral G.hom]
  (hg : CurveFiberHypotheses.NodalGenusOneGeometricFibers G.hom)
  (s : 𝟙_ (Over S) ⟶ G) (hJ : EffectiveCartier s.left.ker)

/-- The original pole step sends the canonical constant to the canonical degree-one vector. -/
theorem relativePoint_initial_step :
    divisorPowerRingStep G.hom.appTop.hom hJ 0 (relativePointZeroBasis G hg s hJ ()) =
      relativePointOneBasis G hg s hJ () := by
  apply (moduleH0Equiv _).injective
  apply (ConcreteCategory.bijective_of_isIso
    ((rightUnitor (divisorLineBundle s.left.ker hJ)).hom.app ⊤)).injective
  apply Eq.trans ?_ (relativePointOneBasis_section G hg s hJ).symm
  rw [divisorPowerRingStep_sections]
  have hz := relativePointZeroBasis_section G hg s hJ
  have hu := structure_leftUnitor_inv_one (X := G.left)
  let d := (divisorTwistedComplex hJ (structureModule G.left)).f
  apply Eq.trans (congrArg (fun z : Γ(G.left, ⊤) ↦
    (rightUnitor (divisorLineBundle s.left.ker hJ)).hom.app ⊤
      (d.app ⊤ ((leftUnitor (structureModule G.left)).inv.app ⊤ z))) hz)
  apply Eq.trans (congrArg (fun z ↦
    (rightUnitor (divisorLineBundle s.left.ker hJ)).hom.app ⊤ (d.app ⊤ z)) hu)
  change (rightUnitor _).hom.app ⊤
    ((map (divisorSectionMap hJ) (𝟙 (structureModule G.left))).app ⊤
      (pure _ _ ⊤ (1 : Γ(G.left, ⊤)) (1 : Γ(G.left, ⊤)))) = _
  rw [map_pure]
  exact (rightUnitor_pure _ ⊤ (1 : Γ(G.left, ⊤)) (divisorSection hJ ⊤)).trans
    (one_smul _ _)

end FLT.Mazur.FCurve.UnrestrictedPole
