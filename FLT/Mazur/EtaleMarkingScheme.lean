/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AuxiliaryLevelFaithfulOpen
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products

/-!
# Markings of an etale group form an etale scheme

Finite powers of etale schemes remain etale. Their group-law equations are
open equalizers, because the target diagonal is open. Removing the nonfaithful
markings is another open restriction. This supplies the etale equation
construction needed for local auxiliary bases.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonObj

namespace FLT.Mazur.EtaleMarkingScheme

variable {S : Scheme}

/-- The actual product in schemes over the base retains etaleness. -/
theorem product_etale {I : Type} [Finite I] (X : I → Over S)
    [∀ i, Etale (X i).hom] : Etale (∏ᶜ X).hom := by
  let _ : Fintype I := Fintype.ofFinite I
  let Y : I → S.Etale := fun i ↦ ⟨X i, inferInstance⟩
  let e := PreservesProduct.iso (Scheme.Etale.forget S) Y
  have : Etale ((Scheme.Etale.forget S).obj (∏ᶜ Y)).hom := (∏ᶜ Y : S.Etale).prop
  have : Etale (e.inv.left ≫ ((Scheme.Etale.forget S).obj (∏ᶜ Y)).hom) := by
    infer_instance
  rw [e.inv.w] at this
  exact this

/-- Equalizer equations with unramified target cut out an open subscheme. -/
theorem equalizer_open {X Y : Over S} [FormallyUnramified Y.hom]
    [LocallyOfFiniteType Y.hom] (f g : X ⟶ Y) :
    IsOpenImmersion (equalizer.ι f g).left := by
  refine MorphismProperty.of_isPullback
    ((isPullback_equalizer_prod f g).map (Over.forget _)).flip ?_
  rw [← MorphismProperty.cancel_right_of_respectsIso @IsOpenImmersion _
    (Over.prodLeftIsoPullback Y Y).hom]
  convert! (inferInstance : IsOpenImmersion (pullback.diagonal Y.hom))
  ext1 <;> simp [← Over.comp_left]

variable (E : Over S) [GrpObj E] [Etale E.hom] (A : Type) [Group A] [Fintype A]

/-- The actual marking equation scheme of an etale group is etale over its base. -/
theorem homScheme_etale : Etale (AuxiliaryLevel.homScheme E A).hom := by
  have : Etale (AuxiliaryLevel.markingPower E A).hom := product_etale _
  have : Etale (∏ᶜ fun _ : A × A ↦ E).hom := product_etale _
  have : IsOpenImmersion (AuxiliaryLevel.homInclusion E A).left :=
    equalizer_open (AuxiliaryLevel.productValues E A) (AuxiliaryLevel.productIndices E A)
  have : Etale ((AuxiliaryLevel.homInclusion E A).left ≫
      (AuxiliaryLevel.markingPower E A).hom) := inferInstance
  rwa [(AuxiliaryLevel.homInclusion E A).w] at this

/-- The universally faithful marking open of an etale group is also etale. -/
theorem faithfulScheme_etale [IsSeparated E.hom] :
    Etale (AuxiliaryLevel.faithfulScheme E A).hom := by
  have := homScheme_etale E A
  change Etale ((AuxiliaryLevel.faithfulOpen E A).ι ≫ (AuxiliaryLevel.homScheme E A).hom)
  infer_instance

end FLT.Mazur.EtaleMarkingScheme
