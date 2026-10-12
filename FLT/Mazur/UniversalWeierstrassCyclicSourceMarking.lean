/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.UniversalWeierstrassCyclicSourceGroupIso
public import FLT.Mazur.OverPullbackSection

/-!
# Every original full cyclic label is compatible with arbitrary source change

The actual source comparison identifies the lifted original section with the
original section of the pulled-back full parameter.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory MonObj
namespace FLT.Mazur.UniversalWeierstrass
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable (n : ℕ) [NeZero n] {T U : Scheme}
  (f : T ⟶ (cyclicAuxiliaryScheme n).left) (k : U ⟶ T)

/-- An original full label, regarded as a relative point over the new source morphism. -/
def cyclicSourceOriginalSection (c : CyclicLabels n) :
    Over.mk k ⟶ (auxiliarySchemeGroup (cyclicSchemeAuxiliaryPoint n f)).X :=
  Over.homMk (k ≫ (cyclicSchemeOriginalMarking n f c).left) (by
    rw [Category.assoc, (cyclicSchemeOriginalMarking n f c).w]
    exact Category.comp_id k)

/-- The universal projection determines every original full label on its actual family. -/
theorem cyclicSchemeOriginalMarking_ext (c : CyclicLabels n)
    (s : 𝟙_ (Over T) ⟶ (auxiliarySchemeGroup (cyclicSchemeAuxiliaryPoint n f)).X)
    (h : s.left ≫ pullback.fst universalGroup.hom
      (cyclicSchemeAuxiliaryPoint n f ≫ levelFour.hom) =
        f ≫ (cyclicAuxiliaryInclusion n ≫
          AuxiliaryLevel.value universalGroup (CyclicLabels n) c).left) :
    s = cyclicSchemeOriginalMarking n f c := by
  apply Over.OverMorphism.ext
  exact pullback.hom_ext (h.trans (cyclicSchemeOriginalMarking_fst n f c).symm)
    (s.w.trans (cyclicSchemeOriginalMarking n f c).w.symm)

/-- Lifting an original full label and comparing source families recovers the actual new label. -/
theorem cyclicSourceOriginalGroupIso_marking (c : CyclicLabels n) :
    OverPullbackSection.lift k (auxiliarySchemeGroup (cyclicSchemeAuxiliaryPoint n f)).X
      (cyclicSourceOriginalSection n f k c) ≫
        (cyclicSourceOriginalGroupIso n f k).hom.hom.hom.hom =
          cyclicSchemeOriginalMarking n (k ≫ f) c := by
  apply cyclicSchemeOriginalMarking_ext
  rw [Over.comp_left, Category.assoc, cyclicSourceOriginalGroupIso_fst,
    ← Category.assoc, OverPullbackSection.lift_fst]
  change (k ≫ (cyclicSchemeOriginalMarking n f c).left) ≫ _ = _
  rw [Category.assoc, cyclicSchemeOriginalMarking_fst, Category.assoc]

end FLT.Mazur.UniversalWeierstrass
