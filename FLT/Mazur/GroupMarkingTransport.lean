/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.CategoryTheory.Monoidal.Cartesian.CommGrp_

/-!
# Transport of full group markings along group-object isomorphisms

Postcomposition transports the complete label homomorphism on every test
object, with an explicit inverse and preservation of injectivity.
-/

@[expose] public noncomputable section

open CategoryTheory MonObj

namespace FLT.Mazur.GroupMarkingTransport

universe u v w
variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]
  [BraidedCategory C]
  {L : Type w} [Monoid L] (G H : CommGrp C) (e : G ≅ H) {T : C}

/-- Postcompose the entire marking with the underlying group morphism. -/
def transport (m : L →* (T ⟶ G.X)) : L →* (T ⟶ H.X) :=
  (IsMonHom.monoidHom e.hom.hom.hom.hom T).comp m

/-- Every label retains the actual postcomposition formula. -/
theorem transport_apply (m : L →* (T ⟶ G.X)) (a : L) :
    transport G H e m a = m a ≫ e.hom.hom.hom.hom := rfl

/-- The inverse isomorphism returns the full original marking. -/
theorem transport_symm_transport (m : L →* (T ⟶ G.X)) :
    transport H G e.symm (transport G H e m) = m := by
  apply MonoidHom.ext
  intro a
  change (m a ≫ e.hom.hom.hom.hom) ≫ e.inv.hom.hom.hom = m a
  have hi : e.hom.hom.hom.hom ≫ e.inv.hom.hom.hom = 𝟙 _ :=
    congrArg (fun f => f.hom.hom.hom) e.hom_inv_id
  rw [Category.assoc, hi, Category.comp_id]

/-- Full group markings are in bijection through an actual group-object isomorphism. -/
def markingEquiv : (L →* (T ⟶ G.X)) ≃ (L →* (T ⟶ H.X)) where
  toFun := transport G H e
  invFun := transport H G e.symm
  left_inv := transport_symm_transport G H e
  right_inv := transport_symm_transport H G e.symm

/-- Transport preserves and reflects faithfulness of the whole label homomorphism. -/
theorem transport_injective_iff (m : L →* (T ⟶ G.X)) :
    Function.Injective (transport G H e m) ↔ Function.Injective m := by
  constructor
  · intro hn a b hab
    apply hn
    exact congrArg (· ≫ e.hom.hom.hom.hom) hab
  · intro hm a b hab
    apply hm
    have he := congrArg (fun f => f ≫ e.inv.hom.hom.hom) hab
    have hr := transport_symm_transport G H e m
    exact (DFunLike.congr_fun hr a).symm.trans (he.trans (DFunLike.congr_fun hr b))

end FLT.Mazur.GroupMarkingTransport
