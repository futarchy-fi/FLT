/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FinitePresentationCancellation
public import FLT.Mazur.SchemeFinitePowerProperties
public import FLT.Mazur.AuxiliaryLevelHomScheme

/-!
# Finite presentation of the full marking scheme

Diagonals of locally finite type morphisms are locally finitely presented,
by cancellation against a pullback projection. Thus the multiplication
equalizer in the finite power is locally finitely presented over every base.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.AuxiliaryLevel
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-- The diagonal of any locally finite type scheme morphism is locally finitely presented. -/
theorem diagonal_locallyOfFinitePresentation {X S : Scheme} (f : X ⟶ S)
    [LocallyOfFiniteType f] : LocallyOfFinitePresentation (pullback.diagonal f) := by
  have h : LocallyOfFinitePresentation (pullback.diagonal f ≫ pullback.fst f f) := by
    rw [pullback.diagonal_fst]
    infer_instance
  exact FinitePresentationCancellation.of_comp (pullback.diagonal f) (pullback.fst f f)

/-- Equality of two maps to a locally finite type relative scheme has finite local equations. -/
theorem equalizerInclusion_locallyOfFinitePresentation {S : Scheme} {X Y : Over S}
    [LocallyOfFiniteType Y.hom] (f g : X ⟶ Y) :
    LocallyOfFinitePresentation (equalizer.ι f g).left := by
  apply MorphismProperty.of_isPullback
    ((Limits.isPullback_equalizer_prod f g).map (Over.forget _)).flip
  rw [← MorphismProperty.cancel_right_of_respectsIso @LocallyOfFinitePresentation _
    (Over.prodLeftIsoPullback Y Y).hom]
  convert! diagonal_locallyOfFinitePresentation Y.hom using 1
  ext1 <;> simp [← Over.comp_left]

variable {S : Scheme} (E : Over S) [GrpObj E] [LocallyOfFinitePresentation E.hom]
  (A : Type) [Group A] [Fintype A]

/-- The actual multiplication relation immersion is locally finitely presented. -/
instance homInclusion_locallyOfFinitePresentation :
    LocallyOfFinitePresentation (homInclusion E A).left := by
  let _ : LocallyOfFiniteType (∏ᶜ fun _ : A × A => E).hom :=
    SchemeFinitePower.property E (@LocallyOfFiniteType) inferInstance (A × A)
  exact equalizerInclusion_locallyOfFinitePresentation (productValues E A) (productIndices E A)

/-- Full markings are locally finitely presented over an arbitrary coefficient base. -/
instance homScheme_locallyOfFinitePresentation :
    LocallyOfFinitePresentation (homScheme E A).hom := by
  let _ : MorphismProperty.IsMultiplicative @LocallyOfFinitePresentation :=
    { id_mem _ := inferInstance }
  let _ : LocallyOfFinitePresentation (markingPower E A).hom :=
    SchemeFinitePower.property E (@LocallyOfFinitePresentation) inferInstance A
  rw [← (homInclusion E A).w]
  infer_instance

end FLT.Mazur.AuxiliaryLevel
