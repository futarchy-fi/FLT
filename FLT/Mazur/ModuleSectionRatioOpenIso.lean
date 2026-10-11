/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ModuleSectionRatioOpen
public import FLT.Mazur.AmpleLineBundle

/-!
# Local section ratios under a specified sheaf isomorphism

Ratios of the original sections are unchanged on every subopen of their
generator open, including for sheaves with different implementations.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Scheme.Modules
universe u
namespace FLT.Mazur.FCurve
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-- A sheaf isomorphism preserves the actual ratio on every generator subopen. -/
theorem sectionRatioOn_iso {X : Scheme.{u}} {L M : X.Modules} (e : L ≅ M)
    (s t : Γ(L, ⊤)) (U : X.Opens) (hU : U ≤ sectionGeneratorOpen L s) :
    sectionRatioOn M (e.hom.app ⊤ s) U
        (by simpa only [sectionGeneratorOpen_iso] using hU) (e.hom.app ⊤ t) =
      sectionRatioOn L s U hU t := by
  apply (sectionRatioOn_eq_iff _ _ _ _ _ _).mpr
  have hs := e.hom.mapPresheaf.naturality (homOfLE (show U ≤ ⊤ from le_top)).op
  have hn (v : Γ(L, ⊤)) :
      M.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op (e.hom.app ⊤ v) =
        e.hom.app U (L.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op v) :=
    (ConcreteCategory.congr_hom hs v).symm
  rw [hn s, hn t, ← Hom.app_smul, sectionRatioOn_smul]

end FLT.Mazur.FCurve
