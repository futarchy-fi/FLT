/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.SchemePairDoubleBoundaryTransfer

/-!
# Order independence of the two boundary changes

Swapping both inputs preserves the exact simultaneous domain. If the target
charts embed in the ambient space, transferring in either order gives the
same full scheme morphism.
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
local notation "E" => domain g f c a

/-- Swapping the inputs exchanges precisely the two original boundary conditions. -/
theorem swap_preimage : (pullbackSymmetry f g).hom ⁻¹ᵁ E = D := by
  unfold domain
  rw [Scheme.Hom.preimage_inf, ← Scheme.Hom.comp_preimage,
    ← Scheme.Hom.comp_preimage, pullbackSymmetry_hom_comp_fst,
    pullbackSymmetry_hom_comp_snd, inf_comm]

/-- The swap of the original relative pair restricts to the entire double boundary. -/
def swapSource : (D).toScheme ⟶ (E).toScheme :=
  IsOpenImmersion.lift (E).ι ((D).ι ≫ (pullbackSymmetry f g).hom) (by
    rintro _ ⟨p, rfl⟩
    rw [Scheme.Opens.range_ι]
    change (pullbackSymmetry f g).hom ((D).ι p) ∈ E
    exact (swap_preimage f g a c).ge p.property)

@[reassoc] theorem swapSource_inclusion :
    swapSource f g a c ≫ (E).ι = (D).ι ≫ (pullbackSymmetry f g).hom :=
  IsOpenImmersion.lift_fac _ _ _

/-- Ambient embeddings determine the transferred pair independently of change order. -/
theorem transfer_swap
    (i : X ⟶ Z) (i' : X' ⟶ Z) [Mono i'] (hi : a ≫ i = b ≫ i')
    (l : Y ⟶ Z) (l' : Y' ⟶ Z) [Mono l'] (hl : c ≫ l = d ≫ l') :
    transfer f f' g g' a b c d h k ≫ (pullbackSymmetry f' g').hom =
      swapSource f g a c ≫ transfer g g' f f' c d a b k h := by
  apply pullback.hom_ext
  · apply (cancel_mono l').mp
    simp only [Category.assoc, pullbackSymmetry_hom_comp_fst_assoc,
      transfer_second_ambient f f' g g' a b c d h k l l' hl,
      transfer_first_ambient g g' f f' c d a b k h l l' hl]
    rw [swapSource_inclusion_assoc,
      pullbackSymmetry_hom_comp_fst_assoc]
  · apply (cancel_mono i').mp
    simp only [Category.assoc, pullbackSymmetry_hom_comp_snd_assoc,
      transfer_first_ambient f f' g g' a b c d h k i i' hi,
      transfer_second_ambient g g' f f' c d a b k h i i' hi]
    rw [swapSource_inclusion_assoc,
      pullbackSymmetry_hom_comp_snd_assoc]

end FLT.Mazur.SchemePairDoubleBoundary
