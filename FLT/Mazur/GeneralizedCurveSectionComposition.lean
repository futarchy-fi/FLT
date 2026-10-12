/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GeneralizedCurveBaseChangeCoherence
public import FLT.Mazur.GroupSectionBaseChange
public import FLT.Mazur.OverPullbackSectionComposition

/-!
# Original markings under composed generalized-curve base change

The full DR composition comparison carries the direct original marking to
its iterated pullback. This lets local presentations retain the original
section when their base neighborhoods are flattened.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory
namespace FLT.Mazur.GeneralizedEllipticCurve
open GroupSectionBaseChange
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {S T U : Scheme} (E : GeneralizedEllipticCurve S)
  (g : T ⟶ S) (h : U ⟶ T) (s : 𝟙_ (Over S) ⟶ E.curve)

/-- The canonical full-curve comparison preserves the actual pulled-back marking. -/
@[reassoc] theorem baseChangeCompIso_section :
    (pullSection (h ≫ g) s).left ≫ (E.baseChangeCompIso g h).hom.curve.left =
      (pullSection h (pullSection g s)).left := by
  let e := (Over.forget U).mapIso ((Over.pullbackComp h g).app E.curve)
  change (pullSection (h ≫ g) s).left ≫ e.hom = _
  apply (cancel_mono e.inv).mp
  simp only [Category.assoc, e.hom_inv_id]
  apply pullback.hom_ext
  · change (pullSection (h ≫ g) s).left ≫ pullback.fst E.curve.hom (h ≫ g) =
      ((pullSection h (pullSection g s)).left ≫
        ((Over.pullbackComp h g).inv.app E.curve).left) ≫ _
    simp only [Category.assoc, OverPullbackSection.comp_inv_fst, section_fst,
      section_fst_assoc]
  · change (pullSection (h ≫ g) s).left ≫ _ =
      ((pullSection h (pullSection g s)).left ≫
        ((Over.pullbackComp h g).inv.app E.curve).left) ≫ _
    have hw : ((Over.pullbackComp h g).inv.app E.curve).left ≫
        pullback.snd E.curve.hom (h ≫ g) =
          pullback.snd (pullback.snd E.curve.hom g) h :=
      ((Over.pullbackComp h g).inv.app E.curve).w
    rw [Category.assoc, hw]
    exact (pullSection (h ≫ g) s).w.trans (pullSection h (pullSection g s)).w.symm

end FLT.Mazur.GeneralizedEllipticCurve
