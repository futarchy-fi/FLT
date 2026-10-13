/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonParameterMarkingLine
public import FLT.Mazur.PolygonParameterTranslationOriginal
public import FLT.Mazur.PolygonTranslationBaseChangeLine

/-!
# Recovery of the original relabeled marking from varying parameters

An original field-valued translation gives precisely the original relabeled
full marking ideal and positive line after every scheme base change.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory
open scoped CategoryTheory.Obj
namespace FLT.Mazur.PolygonParameterTranslation
open PolygonPinching PolygonMarkingBaseChange FCurve
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] translationIso markingIdeal
variable (K : Type) [Field K] (n : ℕ) [NeZero n] (hn : 0 < n)
  {C : Over (Spec (.of K))} (p : components K n ⟶ C) (q : nodes K n ⟶ C)
  (h : IsPushout (toComponents K n hn) (toNodes K n) p q)
  {T : Scheme} (g : T ⟶ Spec (.of K)) (c : Kˣ) (b : ZMod n) (a : Kˣ) (i : Fin n)

/-- Original parameters recover the entire relabeled ideal, with its original multiplicity. -/
theorem movedMarkingIdeal_originalParameter :
    movedMarkingIdeal K n hn p q h g (originalParameter K n g c b) a i =
      markingIdeal K n p g (c * a) (rotateIndex b i) := by
  let e := translationIso K n hn p q h g (originalParameter K n g c b)
  have he : (markingIdeal K n p g (c * a) (rotateIndex b i)).comap e.hom.left =
      markingIdeal K n p g a i := by
    dsimp only [e]
    rw [translationIso_originalParameter_hom]
    exact PolygonMarkingBaseChange.translation_ideal K n hn p q h g c b a i
  have hh := congrArg (fun J ↦ Scheme.IdealSheafData.comap J e.inv.left) he
  rw [← Scheme.IdealSheafData.comap_comp] at hh
  have hi := congrArg Over.Hom.left e.inv_hom_id
  change e.inv.left ≫ e.hom.left = 𝟙 _ at hi
  rw [hi, Scheme.IdealSheafData.comap_id] at hh
  exact hh.symm

/-- The varying construction also recovers the actual original positive line as a sheaf. -/
theorem movedMarkingLine_originalParameter :
    movedMarkingLine K n hn p q h g (originalParameter K n g c b) a i =
      markingLine K n hn p q h g (c * a) (rotateIndex b i) := by
  unfold movedMarkingLine markingLine
  congr 1
  exact movedMarkingIdeal_originalParameter K n hn p q h g c b a i

end FLT.Mazur.PolygonParameterTranslation
