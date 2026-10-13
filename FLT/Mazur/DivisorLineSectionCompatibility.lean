/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.DivisorLinePullback

/-!
# Section compatibility for actual divisor-line comparisons

The predicate keeps the section equation abstract while specializing to large
scheme constructions. Its content is the equality of actual sheaf morphisms.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Scheme.Modules
namespace FLT.Mazur.FCurve
universe u
variable {X Y : Scheme.{u}} {I : Y.IdealSheafData} {J : X.IdealSheafData}

/-- A line comparison preserves the canonical section through the canonical unit map. -/
def DivisorLineSectionCompatible (f : X ⟶ Y) (hI : EffectiveCartier I)
    (hJ : EffectiveCartier J)
    (e : (pullback f).obj (divisorLineBundle I hI) ≅ divisorLineBundle J hJ) : Prop :=
  (pullback f).map (divisorSectionMap hI) ≫ e.hom =
    (modulePullbackUnitIso f).hom ≫ divisorSectionMap hJ

/-- The canonical comparison satisfies the actual section equation. -/
theorem divisorLinePullbackIsoOfEq_compatible (f : X ⟶ Y) (hI : EffectiveCartier I)
    (hJ : EffectiveCartier J) (h : I.comap f = J)
    [IsIso (idealModulePullbackHom I f)] :
    DivisorLineSectionCompatible f hI hJ (divisorLinePullbackIsoOfEq f hI hJ h) :=
  divisorLinePullbackIsoOfEq_section f hI hJ h

/-- Extract the section equation without unfolding the underlying schemes. -/
theorem DivisorLineSectionCompatible.section {f : X ⟶ Y} {hI : EffectiveCartier I}
    {hJ : EffectiveCartier J}
    {e : (pullback f).obj (divisorLineBundle I hI) ≅ divisorLineBundle J hJ}
    (he : DivisorLineSectionCompatible f hI hJ e) :
    (pullback f).map (divisorSectionMap hI) ≫ e.hom =
      (modulePullbackUnitIso f).hom ≫ divisorSectionMap hJ := he

end FLT.Mazur.FCurve
