/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.UniversalWeierstrassCyclicRelationFamilyIso

/-!
# Full marking transport through the sealed normalized comparison

The transport proof is factored through an abstract group isomorphism so that
elaboration does not expand the geometric group laws.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory MonObj
namespace FLT.Mazur.UniversalWeierstrass
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-- Section transport respects equality of group isomorphisms. -/
theorem auxiliarySchemeSection_iso_congr {T : Scheme} {A B : CommGrp (Over T)}
    (s : 𝟙_ (Over T) ⟶ A.X) (t : 𝟙_ (Over T) ⟶ B.X)
    (e d : A ≅ B) (he : e = d) (hs : s ≫ d.hom.hom.hom.hom = t) :
    s ≫ e.hom.hom.hom.hom = t :=
  (congrArg (fun k : A ≅ B ↦ s ≫ k.hom.hom.hom.hom) he).trans hs

attribute [local irreducible] auxiliarySchemeGroup cyclicSchemeOriginalMarking
  cyclicSchemeNormalizedMarking

variable (n : ℕ) [NeZero n] {T : Scheme}
  (f g : T ⟶ (cyclicAuxiliaryScheme n).left)
  (h : cyclicSchemeNormalizedPoint n f = cyclicSchemeNormalizedPoint n g)

/-- The sealed normalized comparison retains every full cyclic label. -/
theorem cyclicRelationNormalizedGroupIso_marking (c : CyclicLabels n) :
    cyclicSchemeNormalizedMarking n f c ≫
      (cyclicRelationNormalizedGroupIso n f g h).hom.hom.hom.hom =
      cyclicSchemeNormalizedMarking n g c :=
  auxiliarySchemeSection_iso_congr (cyclicSchemeNormalizedMarking n f c)
    (cyclicSchemeNormalizedMarking n g c) (cyclicRelationNormalizedGroupIso n f g h)
    (eqToIso (congrArg auxiliarySchemeGroup (cyclicRelation_normalizedAuxiliary_eq n f g h)))
    (cyclicRelationNormalizedGroupIso_def n f g h)
    (cyclicRelation_normalizedMarking_transport n f g h c)

end FLT.Mazur.UniversalWeierstrass
