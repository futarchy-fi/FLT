/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.DivisorLineSectionComposition
public import FLT.Mazur.DivisorLinePullbackIdentity

/-!
# The actual identity comparison preserves the canonical section

The pullback unitor is the section-preserving comparison on an identity map.
Section rigidity identifies every such comparison, including a transport along
an equality of underlying scheme maps, with that original unitor.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Scheme.Modules
namespace FLT.Mazur.FCurve
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {X : Scheme} {I : X.IdealSheafData}

/-- The original pullback unitor preserves the actual divisor section. -/
theorem divisorLineSectionCompatible_id (hI : EffectiveCartier I) :
    DivisorLineSectionCompatible (𝟙 X) hI hI
      ((pullbackId X).app (divisorLineBundle I hI)) := by
  rw [← divisorLinePullbackIsoOfEq_id]
  exact divisorLinePullbackIsoOfEq_compatible _ _ _ _

/-- A section-preserving comparison over the identity is precisely the pullback unitor. -/
theorem DivisorLineSectionCompatible.eq_id {f : X ⟶ X} (w : f = 𝟙 X)
    {hI : EffectiveCartier I}
    {e : (pullback f).obj (divisorLineBundle I hI) ≅ divisorLineBundle I hI}
    (he : DivisorLineSectionCompatible f hI hI e) :
    e = (pullbackCongr w).app _ ≪≫ (pullbackId X).app (divisorLineBundle I hI) :=
  he.ext ((divisorLineSectionCompatible_id hI).congr w)

end FLT.Mazur.FCurve
