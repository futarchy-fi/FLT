/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FreeTargetVanishingFiniteGeneration
public import FLT.Mazur.ProjectiveIdealVanishingScheme
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation

/-!
# Finite presentation of projective coefficient loci

Finite source modules give finitely generated coefficient ideals after a
projective splitting. For a finite algebra this applies to every finitely
generated algebra ideal and yields the original finitely presented closed locus.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.ProjectiveIdealVanishing
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] ProjectiveTargetVanishing.embedding inclusionLinear
variable (R B : Type) [CommRing R] [CommRing B] [Algebra R B]
  [Module.Projective R B] [Module.Finite R B] (J : Ideal B)

/-- Finite algebra-ideal generators give finite equations on the original base ring. -/
theorem ideal_fg (hJ : J.FG) : (ideal R B J).FG := by
  let _ : Module.Finite B J := Module.Finite.iff_fg.mpr hJ
  let _ : Module.Finite R J := Module.Finite.trans B J
  unfold ideal ProjectiveTargetVanishing.ideal
  exact FreeTargetVanishing.ideal_fg (R := R) (M := J) (N := B →₀ R)
    Finsupp.basisSingleOne
    ((ProjectiveTargetVanishing.embedding R B).comp (inclusionLinear R B J))

/-- The actual coefficient quotient is finitely presented without a Noetherian assumption. -/
theorem quotient_finitePresentation (hJ : J.FG) :
    Algebra.FinitePresentation R (R ⧸ ideal R B J) :=
  Algebra.FinitePresentation.quotient (ideal_fg R B J hJ)

/-- The original closed vanishing locus is locally of finite presentation over its base. -/
theorem inclusion_locallyOfFinitePresentation (hJ : J.FG) :
    LocallyOfFinitePresentation (inclusion R B J) := by
  change LocallyOfFinitePresentation
    (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (ideal R B J))))
  let _ := quotient_finitePresentation R B J hJ
  apply (HasRingHomProperty.Spec_iff (P := @LocallyOfFinitePresentation)).mpr
  exact RingHom.finitePresentation_algebraMap.mpr inferInstance

end FLT.Mazur.ProjectiveIdealVanishing
