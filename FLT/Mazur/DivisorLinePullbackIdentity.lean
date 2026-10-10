/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.DivisorLinePullbackComposition
public import FLT.Mazur.CartierIdealPullbackComparison

/-!
# Identity coherence of the canonical divisor-line pullback

The structure-module comparison on an identity is the canonical pullback
unitor. Section rigidity then identifies the divisor-line comparison with
the same unitor.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace FLT.Mazur.FCurve

variable {X : Scheme}

/-- The canonical structure-module comparison for the identity is the pullback unitor. -/
theorem modulePullbackUnitIso_id :
    modulePullbackUnitIso (𝟙 X) = (pullbackId X).app (structureModule X) := by
  apply Iso.ext
  apply ((pullbackPushforwardAdjunction (𝟙 X)).homEquiv _ _).injective
  have hh := unit_conjugateEquiv (Adjunction.id (C := X.Modules))
    (pullbackPushforwardAdjunction (𝟙 X)) (pullbackId X).hom (structureModule X)
  rw [conjugateEquiv_pullbackId_hom] at hh
  calc
    _ = (pushforwardId X).inv.app (structureModule X) := by
      apply Scheme.Modules.hom_ext
      intro U
      ext r
      exact modulePullbackUnitIso_unit (𝟙 X) U r
    _ = _ := hh

/-- The divisor-line identity comparison is exactly the canonical pullback unitor. -/
theorem divisorLinePullbackIsoOfEq_id (I : X.IdealSheafData) (hI : EffectiveCartier I) :
    divisorLinePullbackIsoOfEq (𝟙 X) hI hI (Scheme.IdealSheafData.comap_id I) =
      (pullbackId X).app (divisorLineBundle I hI) := by
  apply divisorLine_iso_ext_unit hI ((pullback (𝟙 X)).map (divisorSectionMap hI))
    (modulePullbackUnitIso (𝟙 X))
  · exact divisorLinePullbackIsoOfEq_section _ _ _ _
  · rw [modulePullbackUnitIso_id]
    exact (pullbackId X).hom.naturality (divisorSectionMap hI)

end FLT.Mazur.FCurve
