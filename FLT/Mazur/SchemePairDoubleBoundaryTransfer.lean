/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.SchemePairDoubleBoundaryDomain

/-!
# Composing both explicit boundary changes

The first transfer followed by the swapped second transfer preserves both
ambient inputs on the full simultaneous boundary open.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.SchemePairDoubleBoundary
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {X X' Y Y' B C S Z : Scheme.{u}}
  (f : X ⟶ S) (f' : X' ⟶ S) (g : Y ⟶ S) (g' : Y' ⟶ S)
  (a : B ⟶ X) [IsOpenImmersion a] (b : B ⟶ X')
  (c : C ⟶ Y) [IsOpenImmersion c] (d : C ⟶ Y')
  (h : a ≫ f = b ≫ f') (k : c ≫ g = d ≫ g')
local notation "D" => domain f g a c
local notation "O" => SchemePairBoundaryTransfer.domain f g a
local notation "E" => SchemePairBoundaryTransfer.domain g f' c

/-- First change the first chart, then change the second chart with factors swapped. -/
def transfer : (D).toScheme ⟶ pullback f' g' :=
  secondStep f f' g a b c h ≫
    SchemePairBoundaryTransfer.transfer g g' f' c d k ≫ (pullbackSymmetry g' f').hom

/-- The first input is exactly the first single-boundary transfer's first input. -/
@[reassoc] theorem transfer_fst :
    transfer f f' g g' a b c d h k ≫ pullback.fst f' g' =
      sourceToFirst f g a c ≫
        SchemePairBoundaryTransfer.transfer f f' g a b h ≫ pullback.fst f' g := by
  rw [transfer, Category.assoc, Category.assoc, pullbackSymmetry_hom_comp_fst,
    SchemePairBoundaryTransfer.transfer_snd, ← Category.assoc, secondStep_inclusion]
  simp only [intermediate, firstStep, Category.assoc, pullbackSymmetry_hom_comp_snd]

/-- The second input is exactly the second single-boundary transfer's first input. -/
@[reassoc] theorem transfer_snd :
    transfer f f' g g' a b c d h k ≫ pullback.snd f' g' =
      secondStep f f' g a b c h ≫
        SchemePairBoundaryTransfer.boundaryInput g f' c ≫ d := by
  rw [transfer, Category.assoc, Category.assoc, pullbackSymmetry_hom_comp_snd,
    SchemePairBoundaryTransfer.transfer_fst]

/-- The composite keeps the entire original first ambient input. -/
@[reassoc] theorem transfer_first_ambient
    (i : X ⟶ Z) (i' : X' ⟶ Z) (hi : a ≫ i = b ≫ i') :
    transfer f f' g g' a b c d h k ≫ pullback.fst f' g' ≫ i' =
      (D).ι ≫ pullback.fst f g ≫ i := by
  rw [transfer_fst_assoc, SchemePairBoundaryTransfer.transfer_first_ambient f f' g a b h
    i i' hi, ← Category.assoc, sourceToFirst_inclusion]

/-- The composite keeps the entire original second ambient input. -/
@[reassoc] theorem transfer_second_ambient
    (i : Y ⟶ Z) (i' : Y' ⟶ Z) (hi : c ≫ i = d ≫ i') :
    transfer f f' g g' a b c d h k ≫ pullback.snd f' g' ≫ i' =
      (D).ι ≫ pullback.snd f g ≫ i := by
  rw [transfer_snd_assoc, ← hi,
    SchemePairBoundaryTransfer.boundaryInput_fac_assoc, secondStep_inclusion_assoc,
    intermediate_first_assoc]

/-- The whole map to the original coefficient scheme is unchanged. -/
@[reassoc] theorem transfer_structure :
    transfer f f' g g' a b c d h k ≫ pullback.fst f' g' ≫ f' =
      (D).ι ≫ pullback.fst f g ≫ f :=
  transfer_first_ambient f f' g g' a b c d h k f f' h

end FLT.Mazur.SchemePairDoubleBoundary
