/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OneGonSmoothingFullAuxiliaryMarking
public import FLT.Mazur.OneGonSmoothingAuxiliaryOverlap

/-!
# The complete auxiliary group marking on the actual boundary overlap

Every scheme mapping to the actual etale overlap inherits the original boundary
group by base change. Its complete marking is constructed from the retained
auxiliary point, with no choice of an affine presentation of the source.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory MonObj
namespace FLT.Mazur.OneGonSmoothing
open UniversalWeierstrass WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R]
  (t : R) (h₂ : IsUnit (2 : R)) (ht : IsUnit t) (hf : IsUnit (1 + 432 * t))
  {T : Scheme} (j : T ⟶ smoothAuxiliaryOverlap t h₂ ht hf)

/-- The entire original boundary group pulled back to an arbitrary overlap test scheme. -/
def smoothOverlapGroup : CommGrp (Over T) :=
  (Over.pullback (j ≫ smoothAuxiliaryProjection t h₂ ht hf)).mapCommGrp.obj
    (smoothGroup t ht hf)

/-- The actual auxiliary point retained over both original coefficient bases. -/
def smoothOverlapRelativePoint :
    (Over.map (Spec.map (CommRingCat.ofHom (smoothParameter t h₂ ht hf)))).obj
      ((Over.map (j ≫ smoothAuxiliaryProjection t h₂ ht hf)).obj (𝟙_ (Over T))) ⟶
        levelFour :=
  Over.homMk (j ≫ smoothAuxiliaryPoint t h₂ ht hf) (by
    change (j ≫ smoothAuxiliaryPoint t h₂ ht hf) ≫ levelFour.hom =
      (𝟙 T ≫ (j ≫ smoothAuxiliaryProjection t h₂ ht hf)) ≫ _
    rw [Category.id_comp, Category.assoc, smoothAuxiliaryPoint_base, Category.assoc]
    rfl)

/-- Every auxiliary label is an actual section of the original boundary group over the test. -/
def smoothOverlapMarking : Labels 4 →* (𝟙_ (Over T) ⟶ (smoothOverlapGroup t h₂ ht hf j).X) :=
  GroupMarkingBaseChange.marking (j ≫ smoothAuxiliaryProjection t h₂ ht hf)
    (smoothGroup t ht hf).X (𝟙_ (Over T))
    (smoothFullMarking t h₂ ht hf (smoothOverlapRelativePoint t h₂ ht hf j))

/-- The full overlap marking retains its original section after boundary projection. -/
@[reassoc] theorem smoothOverlapMarking_fst (a : Labels 4) :
    (smoothOverlapMarking t h₂ ht hf j a).left ≫
      pullback.fst (family t).hom (j ≫ smoothAuxiliaryProjection t h₂ ht hf) =
        (smoothFullMarking t h₂ ht hf (smoothOverlapRelativePoint t h₂ ht hf j) a).left :=
  GroupMarkingBaseChange.marking_fst _ _ _ _ a

/-- Projection to the universal cubic retains every original auxiliary scheme marking. -/
@[reassoc] theorem smoothOverlapMarking_universal (a : Labels 4) :
    (smoothOverlapMarking t h₂ ht hf j a).left ≫
      pullback.fst (family t).hom (j ≫ smoothAuxiliaryProjection t h₂ ht hf) ≫
        smoothUniversalMorphism t h₂ ht hf =
          (j ≫ smoothAuxiliaryPoint t h₂ ht hf) ≫ (auxiliaryMarking 4 a).left := by
  rw [← Category.assoc, smoothOverlapMarking_fst]
  exact smoothFullMarking_universal t h₂ ht hf _ a

/-- All sixteen actual overlap sections remain distinct on every nonempty source. -/
theorem smoothOverlapMarking_injective [Nonempty T] :
    Function.Injective (smoothOverlapMarking t h₂ ht hf j) := by
  unfold smoothOverlapMarking
  apply (GroupMarkingBaseChange.marking_injective_iff _ _ _ _).mpr
  let _ : Nonempty ((Over.map (j ≫ smoothAuxiliaryProjection t h₂ ht hf)).obj
    (𝟙_ (Over T))).left := inferInstanceAs (Nonempty T)
  exact smoothFullMarking_injective t h₂ ht hf _

/-- The complete auxiliary marking is killed by four in the actual pulled-back group. -/
theorem smoothOverlapMarking_pow (a : Labels 4) :
    smoothOverlapMarking t h₂ ht hf j a ^ 4 = 1 :=
  GroupMarkingTransport.marking_pow_eq_one _ (smoothOverlapMarking t h₂ ht hf j) a 4
    (labels_pow 4 a)

end FLT.Mazur.OneGonSmoothing
