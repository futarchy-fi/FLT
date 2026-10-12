/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.UniversalWeierstrassCyclicRelationNormalizedMarking

/-!
# The canonical relation comparison preserves the original full marking

The transport proof is factored through an abstract group isomorphism so that
elaboration does not expand the geometric group laws.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory MonObj
namespace FLT.Mazur.UniversalWeierstrass
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-- Conjugation by group comparisons transports sections without geometric unfolding. -/
theorem auxiliarySchemeSection_conjugate {T : Scheme} {A B C D : CommGrp (Over T)}
    (e : A ≅ B) (d : A ≅ C) (k : C ≅ D)
    (s : 𝟙_ (Over T) ⟶ B.X) (t : 𝟙_ (Over T) ⟶ A.X)
    (u : 𝟙_ (Over T) ⟶ C.X) (v : 𝟙_ (Over T) ⟶ D.X)
    (ht : t ≫ e.hom.hom.hom.hom = s) (hd : t ≫ d.hom.hom.hom.hom = u)
    (hv : u ≫ k.hom.hom.hom.hom = v) :
    s ≫ (e.symm ≪≫ d ≪≫ k).hom.hom.hom.hom = v := by
  have hi : e.hom.hom.hom.hom ≫ e.inv.hom.hom.hom = 𝟙 _ :=
    congrArg (fun z ↦ z.hom.hom.hom) e.hom_inv_id
  rw [auxiliarySchemeGroupIso_composite_hom, ← ht]
  simp only [Category.assoc, ← Category.assoc e.hom.hom.hom.hom, hi, Category.id_comp]
  rw [← Category.assoc, hd, hv]

attribute [local irreducible] auxiliarySchemeGroup cyclicSchemeOriginalMarking
  cyclicSchemeNormalizedMarking

variable (n : ℕ) [NeZero n] {T : Scheme}
  (f g : T ⟶ (cyclicAuxiliaryScheme n).left)
  (h : cyclicSchemeNormalizedPoint n f = cyclicSchemeNormalizedPoint n g)

/-- The canonical group comparison preserves every original full cyclic label. -/
theorem cyclicRelationFamilyIso_marking (c : CyclicLabels n) :
    cyclicSchemeOriginalMarking n f c ≫ (cyclicRelationFamilyIso n f g h).hom.hom.hom.hom =
      cyclicSchemeOriginalMarking n g c :=
  auxiliarySchemeSection_iso_congr (cyclicSchemeOriginalMarking n f c)
    (cyclicSchemeOriginalMarking n g c) (cyclicRelationFamilyIso n f g h) _
    (cyclicRelationFamilyIso_def n f g h)
    (auxiliarySchemeSection_conjugate
      (auxiliarySchemeNormalizationGroupIso (cyclicSchemeAuxiliaryPoint n f))
      (cyclicRelationNormalizedGroupIso n f g h)
      (auxiliarySchemeNormalizationGroupIso (cyclicSchemeAuxiliaryPoint n g))
      (cyclicSchemeOriginalMarking n f c) (cyclicSchemeNormalizedMarking n f c)
      (cyclicSchemeNormalizedMarking n g c) (cyclicSchemeOriginalMarking n g c)
      (cyclicSchemeNormalizedMarking_compare n f c)
      (cyclicRelationNormalizedGroupIso_marking n f g h c)
      (cyclicSchemeNormalizedMarking_compare n g c))

end FLT.Mazur.UniversalWeierstrass
