/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CartierIdealPullbackComparison
public import FLT.Mazur.DivisorLinePullbackTransport
public import FLT.Mazur.SectionGradedLineRingCoherence

/-!
# Canonical Cartier section rings on a commutative square

The actual dual-ideal comparisons give functorial maps of all tensor-degree
sections. A square preserving the Cartier ideals therefore preserves these maps.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Scheme.Modules
namespace FLT.Mazur.FCurve
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {X Y Z W : Scheme}

/-- The canonical section-ring map for a morphism preserving the Cartier ideal. -/
def cartierSectionRingMap (f : X ⟶ Y) {I : Y.IdealSheafData} {J : X.IdealSheafData}
    (hI : EffectiveCartier I) (hJ : EffectiveCartier J) (hf : I.comap f = J) :
    SectionGradedSum.Sections (divisorLineBundle I hI) ⊤ →+*
      SectionGradedSum.Sections (divisorLineBundle J hJ) ⊤ := by
  let _ : IsIso (idealModulePullbackHom I f) :=
    idealModulePullbackHom_isIso_of_cartier f hI (hf.symm ▸ hJ)
  exact SectionGradedLinePullback.ringHom f (divisorLinePullbackIsoOfEq f hI hJ hf)

/-- Canonical Cartier section pullbacks compose on every tensor degree. -/
theorem cartierSectionRingMap_comp (f : X ⟶ Y) (g : Y ⟶ Z)
    {I : Z.IdealSheafData} {J : Y.IdealSheafData} {K : X.IdealSheafData}
    (hI : EffectiveCartier I) (hJ : EffectiveCartier J) (hK : EffectiveCartier K)
    (hg : I.comap g = J) (hf : J.comap f = K) (hfg : I.comap (f ≫ g) = K) :
    cartierSectionRingMap (f ≫ g) hI hK hfg =
      (cartierSectionRingMap f hJ hK hf).comp (cartierSectionRingMap g hI hJ hg) := by
  let _ : IsIso (idealModulePullbackHom I g) :=
    idealModulePullbackHom_isIso_of_cartier g hI (hg.symm ▸ hJ)
  let _ : IsIso (idealModulePullbackHom J f) :=
    idealModulePullbackHom_isIso_of_cartier f hJ (hf.symm ▸ hK)
  let _ : IsIso (idealModulePullbackHom I (f ≫ g)) :=
    idealModulePullbackHom_isIso_of_cartier (f ≫ g) hI (hfg.symm ▸ hK)
  exact SectionGradedLinePullback.ringHom_comp_eq f g (f ≫ g) rfl _ _ _
    (divisorLinePullbackIsoOfEq_comp_eq f g (f ≫ g) rfl hI hJ hK hg hf hfg)

/-- A commutative square retaining its four Cartier ideals retains all section-ring maps. -/
theorem cartierSectionRingMap_square (f : X ⟶ Y) (g : Y ⟶ W)
    (f' : X ⟶ Z) (g' : Z ⟶ W) (hw : f ≫ g = f' ≫ g')
    {I : W.IdealSheafData} {J : Y.IdealSheafData}
    {K : Z.IdealSheafData} {L : X.IdealSheafData}
    (hI : EffectiveCartier I) (hJ : EffectiveCartier J)
    (hK : EffectiveCartier K) (hL : EffectiveCartier L)
    (hg : I.comap g = J) (hf : J.comap f = L)
    (hg' : I.comap g' = K) (hf' : K.comap f' = L) :
    (cartierSectionRingMap f hJ hL hf).comp (cartierSectionRingMap g hI hJ hg) =
      (cartierSectionRingMap f' hK hL hf').comp (cartierSectionRingMap g' hI hK hg') := by
  have hc : I.comap (f ≫ g) = L := by rw [Scheme.IdealSheafData.comap_comp, hg, hf]
  have hc' : I.comap (f' ≫ g') = L := by rw [← hw, hc]
  rw [← cartierSectionRingMap_comp f g hI hJ hL hg hf hc,
    ← cartierSectionRingMap_comp f' g' hI hK hL hg' hf' hc']
  congr 1

end FLT.Mazur.FCurve
