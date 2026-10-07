/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeAffineChartBaseChange

/-!
# A constructed common cover over an affine overlap

Base change each original covering ring to the common affine base, then take
their ring pushout (the tensor product). This constructs a cross refinement
without any identification of the original covering maps into Y.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace FLT.Mazur.SchemeAffineDescent.Chart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {X Y : Scheme.{u}} {p : Y ⟶ X} (C C' : Chart p)
variable {A : CommRingCat.{u}} (f : C.baseRing ⟶ A) (g : C'.baseRing ⟶ A)

/-- The common cover ring is the pushout of the two base-changed covering rings. -/
def commonCoverRing : CommRingCat.{u} :=
  pushout (C.baseChange f).ringMap (C'.baseChange g).ringMap

/-- First projection of the common cover, in ring coordinates. -/
def commonCoverLeft : C.coverRing ⟶ C.commonCoverRing C' f g :=
  (C.baseChangeRefinement f).cover ≫
    pushout.inl (C.baseChange f).ringMap (C'.baseChange g).ringMap

/-- Second projection of the common cover, retaining its independent map into Y. -/
def commonCoverRight : C'.coverRing ⟶ C.commonCoverRing C' f g :=
  (C'.baseChangeRefinement g).cover ≫
    pushout.inr (C.baseChange f).ringMap (C'.baseChange g).ringMap

/-- The constructed common covering map over the overlap ring. -/
def commonCoverMap : A ⟶ C.commonCoverRing C' f g :=
  (C.baseChange f).ringMap ≫
    pushout.inl (C.baseChange f).ringMap (C'.baseChange g).ringMap

/-- Both successive covering maps are faithfully flat. -/
theorem commonCoverMap_faithfullyFlat : (C.commonCoverMap C' f g).hom.FaithfullyFlat :=
  RingHom.FaithfullyFlat.stableUnderComposition _ _ (C.baseChange f).faithfullyFlat
    (RingHom.FaithfullyFlat.isStableUnderBaseChange.pushout_inl
      RingHom.FaithfullyFlat.respectsIso _ _ (C'.baseChange g).faithfullyFlat)

/-- The first original chart factors through the common covering map. -/
theorem commonCoverLeft_square :
    C.ringMap ≫ C.commonCoverLeft C' f g = f ≫ C.commonCoverMap C' f g := by
  dsimp only [commonCoverLeft, commonCoverMap]
  rw [← Category.assoc, (C.baseChangeRefinement f).square, Category.assoc]
  rfl

/-- The second original chart factors through the same common covering map. -/
theorem commonCoverRight_square :
    C'.ringMap ≫ C.commonCoverRight C' f g = g ≫ C.commonCoverMap C' f g := by
  dsimp only [commonCoverRight, commonCoverMap]
  rw [← Category.assoc, (C'.baseChangeRefinement g).square, Category.assoc,
    ← pushout.condition]
  rfl

variable (w : Spec.map f ≫ C.base = Spec.map g ≫ C'.base)

/-- Every common affine base of two charts has a constructed faithfully flat cross cover. -/
def commonBaseCrossRefinement : C.CrossRefinement C' where
  baseRing := A
  coverRing := C.commonCoverRing C' f g
  ringMap := C.commonCoverMap C' f g
  faithfullyFlat := C.commonCoverMap_faithfullyFlat C' f g
  leftBase := f
  rightBase := g
  leftCover := C.commonCoverLeft C' f g
  rightCover := C.commonCoverRight C' f g
  leftSquare := C.commonCoverLeft_square C' f g
  rightSquare := C.commonCoverRight_square C' f g
  base_over := w

end FLT.Mazur.SchemeAffineDescent.Chart
