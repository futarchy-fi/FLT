/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.SchemePairBoundaryTransfer

/-!
# The exact domain for two successive boundary changes

Changing the first input and then the second requires precisely the
intersection of the two original boundary preimages.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.SchemePairDoubleBoundary
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {X X' Y Y' B C S : Scheme.{u}}
  (f : X ⟶ S) (f' : X' ⟶ S) (g : Y ⟶ S) (g' : Y' ⟶ S)
  (a : B ⟶ X) [IsOpenImmersion a] (b : B ⟶ X')
  (c : C ⟶ Y) [IsOpenImmersion c] (d : C ⟶ Y')
  (h : a ≫ f = b ≫ f') (k : c ≫ g = d ≫ g')

/-- The full simultaneous boundary domain in the original relative pair. -/
def domain : (pullback f g).Opens :=
  pullback.fst f g ⁻¹ᵁ a.opensRange ⊓ pullback.snd f g ⁻¹ᵁ c.opensRange

local notation "D" => domain f g a c
local notation "O" => SchemePairBoundaryTransfer.domain f g a
local notation "E" => SchemePairBoundaryTransfer.domain g f' c

/-- The first transfer, with factors swapped to prepare the second transfer. -/
def firstStep : (O).toScheme ⟶ pullback g f' :=
  SchemePairBoundaryTransfer.transfer f f' g a b h ≫ (pullbackSymmetry f' g).hom

/-- The next domain tests the original second input, with no added condition. -/
theorem firstStep_preimage :
    firstStep f f' g a b h ⁻¹ᵁ E =
      (O).ι ⁻¹ᵁ (pullback.snd f g ⁻¹ᵁ c.opensRange) := by
  unfold SchemePairBoundaryTransfer.domain
  rw [← Scheme.Hom.comp_preimage, firstStep, Category.assoc,
    pullbackSymmetry_hom_comp_fst, SchemePairBoundaryTransfer.transfer_snd]
  rw [Scheme.Hom.comp_preimage]
  rfl

/-- Restriction of the original pair to both boundary conditions. -/
def sourceToFirst : (D).toScheme ⟶ (O).toScheme :=
  (pullback f g).homOfLE inf_le_left

@[reassoc] theorem sourceToFirst_inclusion :
    sourceToFirst f g a c ≫ (O).ι = (D).ι := Scheme.homOfLE_ι _ _

/-- The first transfer is defined on the complete simultaneous boundary open. -/
def intermediate : (D).toScheme ⟶ pullback g f' :=
  sourceToFirst f g a c ≫ firstStep f f' g a b h

/-- The swapped first input is exactly the original second input. -/
@[reassoc] theorem intermediate_first :
    intermediate f f' g a b c h ≫ pullback.fst g f' =
      (D).ι ≫ pullback.snd f g := by
  rw [intermediate, firstStep, Category.assoc, Category.assoc,
    pullbackSymmetry_hom_comp_fst, SchemePairBoundaryTransfer.transfer_snd,
    ← Category.assoc, sourceToFirst_inclusion]

/-- The second boundary lift exists everywhere on the simultaneous domain. -/
def secondStep : (D).toScheme ⟶ (E).toScheme :=
  IsOpenImmersion.lift (E).ι (intermediate f f' g a b c h) (by
    rintro _ ⟨p, rfl⟩
    rw [Scheme.Opens.range_ι]
    change pullback.fst g f' (intermediate f f' g a b c h p) ∈ Set.range c
    have he := congrArg (fun t => t p) (intermediate_first f f' g a b c h)
    exact he ▸ p.property.2)

/-- The second lift retains the entire result of the first transfer. -/
@[reassoc] theorem secondStep_inclusion :
    secondStep f f' g a b c h ≫ (E).ι = intermediate f f' g a b c h :=
  IsOpenImmersion.lift_fac _ _ _

end FLT.Mazur.SchemePairDoubleBoundary
