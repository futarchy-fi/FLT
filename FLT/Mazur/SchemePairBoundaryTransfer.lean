/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion

/-!
# Changing one input chart on its full boundary domain

An actual common boundary induces a morphism on the corresponding open of
the whole relative pair. Both ambient inputs and every function on them are
preserved. No pointwise choice of coordinates is used to define the map.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.SchemePairBoundaryTransfer
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {X X' Y B S Z : Scheme.{u}}
  (f : X ⟶ S) (f' : X' ⟶ S) (g : Y ⟶ S)
  (a : B ⟶ X) [IsOpenImmersion a] (b : B ⟶ X')
  (h : a ≫ f = b ≫ f')

/-- The entire inverse image of the boundary in the original relative pair. -/
def domain : (pullback f g).Opens := pullback.fst f g ⁻¹ᵁ a.opensRange

local notation "O" => domain f g a

/-- Membership tests only the original first input's membership in the full boundary. -/
theorem mem_domain (p : (pullback f g : Scheme)) :
    p ∈ O ↔ pullback.fst f g p ∈ Set.range a := Iff.rfl

/-- The actual boundary-valued first input on this open. -/
def boundaryInput : (O).toScheme ⟶ B :=
  IsOpenImmersion.lift a ((O).ι ≫ pullback.fst f g) (by
    rintro _ ⟨p, rfl⟩
    exact p.property)

/-- Factoring the first input preserves its entire original morphism. -/
@[reassoc] theorem boundaryInput_fac :
    boundaryInput f g a ≫ a = (O).ι ≫ pullback.fst f g :=
  IsOpenImmersion.lift_fac _ _ _

/-- The common boundary changes the first chart on the whole pair open. -/
def transfer : (O).toScheme ⟶ pullback f' g :=
  pullback.lift (boundaryInput f g a ≫ b) ((O).ι ≫ pullback.snd f g) (by
    rw [Category.assoc, ← h, ← Category.assoc, boundaryInput_fac,
      Category.assoc, pullback.condition, ← Category.assoc])

/-- The first projection is the full boundary transition, with all its functions. -/
@[reassoc] theorem transfer_fst :
    transfer f f' g a b h ≫ pullback.fst f' g = boundaryInput f g a ≫ b :=
  pullback.lift_fst _ _ _

/-- The second input remains its original morphism throughout the transfer. -/
@[reassoc] theorem transfer_snd :
    transfer f f' g a b h ≫ pullback.snd f' g = (O).ι ≫ pullback.snd f g :=
  pullback.lift_snd _ _ _

/-- The original coefficient point is retained on the whole open domain. -/
@[reassoc] theorem transfer_structure :
    transfer f f' g a b h ≫ pullback.fst f' g ≫ f' =
      (O).ι ≫ pullback.fst f g ≫ f := by
  rw [transfer_fst_assoc, ← h, ← Category.assoc, boundaryInput_fac, Category.assoc]

variable (i : X ⟶ Z) (i' : X' ⟶ Z) (hi : a ≫ i = b ≫ i')

include hi in
/-- The new first coordinates represent precisely the original ambient input. -/
@[reassoc] theorem transfer_first_ambient :
    transfer f f' g a b h ≫ pullback.fst f' g ≫ i' =
      (O).ι ≫ pullback.fst f g ≫ i := by
  rw [transfer_fst_assoc, ← hi, ← Category.assoc, boundaryInput_fac, Category.assoc]

end FLT.Mazur.SchemePairBoundaryTransfer
