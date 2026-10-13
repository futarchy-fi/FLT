/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.DivisorLineSectionCompatibility
public import FLT.Mazur.DivisorLinePullbackComposition

/-!
# Composition and uniqueness of section-preserving line comparisons

Section rigidity gives coherence for concrete comparisons without unfolding
those comparisons into their ideal-sheaf constructions.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Scheme.Modules
namespace FLT.Mazur.FCurve
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {X Y Z : Scheme} {I : Z.IdealSheafData} {J : Y.IdealSheafData}
  {K : X.IdealSheafData}

/-- Two comparisons preserving the canonical section are equal as isomorphisms. -/
theorem DivisorLineSectionCompatible.ext {f : X ⟶ Y}
    {hJ : EffectiveCartier J} {hK : EffectiveCartier K}
    {e e' : (pullback f).obj (divisorLineBundle J hJ) ≅ divisorLineBundle K hK}
    (he : DivisorLineSectionCompatible f hJ hK e)
    (he' : DivisorLineSectionCompatible f hJ hK e') : e = e' :=
  divisorLine_iso_ext_unit hK ((pullback f).map (divisorSectionMap hJ))
    (modulePullbackUnitIso f) e e' he.section he'.section

/-- Composition through the actual pullback compositor preserves the section. -/
theorem DivisorLineSectionCompatible.comp {f : X ⟶ Y} {g : Y ⟶ Z}
    {hI : EffectiveCartier I} {hJ : EffectiveCartier J} {hK : EffectiveCartier K}
    {e : (pullback g).obj (divisorLineBundle I hI) ≅ divisorLineBundle J hJ}
    {v : (pullback f).obj (divisorLineBundle J hJ) ≅ divisorLineBundle K hK}
    (he : DivisorLineSectionCompatible g hI hJ e)
    (hv : DivisorLineSectionCompatible f hJ hK v) :
    DivisorLineSectionCompatible (f ≫ g) hI hK
      ((pullbackComp f g).symm.app _ ≪≫ (pullback f).mapIso e ≪≫ v) := by
  change _ ≫ (pullbackComp f g).inv.app _ ≫ (pullback f).map e.hom ≫ v.hom = _
  have hn := (pullbackComp f g).inv.naturality (divisorSectionMap hI)
  dsimp only [Functor.comp_map] at hn
  rw [← Category.assoc, hn, Category.assoc, ← Functor.map_comp_assoc,
    he.section, Functor.map_comp, Category.assoc, hv.section]
  rw [← Category.assoc ((pullback f).map (modulePullbackUnitIso g).hom),
    modulePullbackUnitIso_comp_hom, Category.assoc, Iso.inv_hom_id_app_assoc]

/-- Transport along equality of scheme maps preserves the section comparison. -/
theorem DivisorLineSectionCompatible.congr {f g : X ⟶ Y} (hfg : f = g)
    {hJ : EffectiveCartier J} {hK : EffectiveCartier K}
    {e : (pullback g).obj (divisorLineBundle J hJ) ≅ divisorLineBundle K hK}
    (he : DivisorLineSectionCompatible g hJ hK e) :
    DivisorLineSectionCompatible f hJ hK ((pullbackCongr hfg).app _ ≪≫ e) := by
  subst g
  simpa [DivisorLineSectionCompatible, pullbackCongr] using he.section

end FLT.Mazur.FCurve
