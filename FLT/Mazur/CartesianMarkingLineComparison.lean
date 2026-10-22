/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SectionPointLineCoherence
public import FLT.Mazur.DivisorLinePullbackComposition

/-!
# Canonical line comparison on a common pointed refinement

Two Cartesian models of the same marking have canonically isomorphic
pulled-back divisor lines. The comparison preserves the actual vanishing
sections, and section rigidity makes that comparison unique.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Scheme.Modules
namespace FLT.Mazur.FCurve
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] divisorLineBundle Scheme.Modules.pullback sectionPointLineIso

variable {W X Y T A B : Scheme}
  {v : W ⟶ T} {p : X ⟶ A} {q : Y ⟶ B}
  {c : W ⟶ X} {d : W ⟶ Y} {a : T ⟶ A} {b : T ⟶ B}
  [IsSeparated p] [IsSeparated q]
  (hc : IsPullback c v p a) (hd : IsPullback d v q b)
  (t : T ⟶ W) (s : A ⟶ X) (u : B ⟶ Y)
  (ht : t ≫ v = 𝟙 _) (hs : s ≫ p = 𝟙 _) (hu : u ≫ q = 𝟙 _)
  (hcs : t ≫ c = a ≫ s) (hdu : t ≫ d = b ≫ u)
  (hI : EffectiveCartier s.ker) (hJ : EffectiveCartier u.ker) (hK : EffectiveCartier t.ker)

/-- The canonical comparison of two model lines through the actual common marking. -/
def commonMarkingLineIso :
    (pullback c).obj (divisorLineBundle s.ker hI) ≅
      (pullback d).obj (divisorLineBundle u.ker hJ) :=
  sectionPointLineIso hc s t hs ht hcs hI hK ≪≫
    (sectionPointLineIso hd u t hu ht hdu hJ hK).symm

/-- The comparison retains both model sections and their structure-module identifications. -/
theorem commonMarkingLineIso_section :
    (pullback c).map (divisorSectionMap hI) ≫
        (commonMarkingLineIso hc hd t s u ht hs hu hcs hdu hI hJ hK).hom =
      (modulePullbackUnitIso c).hom ≫ (modulePullbackUnitIso d).inv ≫
        (pullback d).map (divisorSectionMap hJ) := by
  simp only [commonMarkingLineIso, Iso.trans_hom, Iso.symm_hom]
  rw [← Category.assoc, sectionPointLineIso_section]
  have he := sectionPointLineIso_section hd u t hu ht hdu hJ hK
  rw [← cancel_mono (sectionPointLineIso hd u t hu ht hdu hJ hK).hom]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [he, Iso.inv_hom_id_assoc]

/-- No other comparison can preserve those two canonical vanishing sections. -/
theorem commonMarkingLineIso_unique
    (e : (pullback c).obj (divisorLineBundle s.ker hI) ≅
      (pullback d).obj (divisorLineBundle u.ker hJ))
    (he : (pullback c).map (divisorSectionMap hI) ≫ e.hom =
      (modulePullbackUnitIso c).hom ≫ (modulePullbackUnitIso d).inv ≫
        (pullback d).map (divisorSectionMap hJ)) :
    e = commonMarkingLineIso hc hd t s u ht hs hu hcs hdu hI hJ hK := by
  have h := divisorLine_iso_ext_unit hK ((pullback c).map (divisorSectionMap hI))
    (modulePullbackUnitIso c)
    (e ≪≫ sectionPointLineIso hd u t hu ht hdu hJ hK)
    (sectionPointLineIso hc s t hs ht hcs hI hK) (by
      rw [Iso.trans_hom, ← Category.assoc, he]
      simp only [Category.assoc]
      rw [sectionPointLineIso_section, Iso.inv_hom_id_assoc])
    (sectionPointLineIso_section hc s t hs ht hcs hI hK)
  calc
    e = (e ≪≫ sectionPointLineIso hd u t hu ht hdu hJ hK) ≪≫
        (sectionPointLineIso hd u t hu ht hdu hJ hK).symm := by simp
    _ = _ := by rw [h]; rfl

end FLT.Mazur.FCurve
