/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.DivisorSectionRigidity
public import FLT.Mazur.DivisorLinePullback

/-!
# Composition coherence of the canonical divisor-line pullbacks

The actual dual ideal comparisons obey composition. Section preservation and
regular-section rigidity prove the law without unfolding tensor constructions.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace FLT.Mazur.FCurve

variable {X Y Z : Scheme} {I : Z.IdealSheafData} {J : Y.IdealSheafData}
variable {K : X.IdealSheafData}

/-- Section rigidity also applies when the section source has a specified unit comparison. -/
theorem divisorLine_iso_ext_unit {A L : X.Modules} (hK : EffectiveCartier K)
    (s : A ⟶ L) (u : A ≅ structureModule X) (e e' : L ≅ divisorLineBundle K hK)
    (he : s ≫ e.hom = u.hom ≫ divisorSectionMap hK)
    (he' : s ≫ e'.hom = u.hom ≫ divisorSectionMap hK) : e = e' := by
  apply divisorLine_iso_ext hK (u.inv ≫ s)
  · rw [Category.assoc, he, Iso.inv_hom_id_assoc]
  · rw [Category.assoc, he', Iso.inv_hom_id_assoc]

/-- Canonical divisor-line comparisons compose through the actual pullback compositor. -/
theorem divisorLinePullbackIsoOfEq_comp (f : X ⟶ Y) (g : Y ⟶ Z)
    (hI : EffectiveCartier I) (hJ : EffectiveCartier J) (hK : EffectiveCartier K)
    (hg : I.comap g = J) (hf : J.comap f = K) (hfg : I.comap (f ≫ g) = K)
    [IsIso (idealModulePullbackHom I g)] [IsIso (idealModulePullbackHom J f)]
    [IsIso (idealModulePullbackHom I (f ≫ g))] :
    (pullback f).mapIso (divisorLinePullbackIsoOfEq g hI hJ hg) ≪≫
        divisorLinePullbackIsoOfEq f hJ hK hf =
      (pullbackComp f g).app (divisorLineBundle I hI) ≪≫
        divisorLinePullbackIsoOfEq (f ≫ g) hI hK hfg := by
  apply divisorLine_iso_ext_unit hK
    ((pullback f).map ((pullback g).map (divisorSectionMap hI)))
    ((pullback f).mapIso (modulePullbackUnitIso g) ≪≫ modulePullbackUnitIso f)
  · simp only [Iso.trans_hom, Functor.mapIso_hom, ← Functor.map_comp_assoc]
    rw [divisorLinePullbackIsoOfEq_section, Functor.map_comp, Category.assoc,
      divisorLinePullbackIsoOfEq_section]
    simp only [Category.assoc]
  · simp only [Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom]
    have hn := (pullbackComp f g).hom.naturality (divisorSectionMap hI)
    dsimp only [Functor.comp_map] at hn
    rw [← Category.assoc, hn]
    simp only [Category.assoc]
    rw [divisorLinePullbackIsoOfEq_section]
    rw [← Category.assoc, ← modulePullbackUnitIso_comp_hom]
    simp only [Category.assoc]

end FLT.Mazur.FCurve
