/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GroupMarkingTransport

/-!
# Naturality of complete markings transported through group isomorphisms

Postcomposition through a fixed group isomorphism commutes with every change
of test object. Keeping the argument abstract avoids unfolding concrete
geometric group operations in naturality proofs.
-/

@[expose] public noncomputable section

open CategoryTheory MonObj

namespace FLT.Mazur.GroupMarkingTransport

universe u v w
variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]
  [BraidedCategory C] {L : Type w} [Monoid L]
  (G H : CommGrp C) (e : G ≅ H) {U T : C}

/-- Transport of a full marking commutes with pullback of every labeled section. -/
theorem transport_natural (k : U ⟶ T) (m : L →* (T ⟶ G.X)) (n : L →* (U ⟶ G.X))
    (hn : ∀ a, n a = k ≫ m a) (a : L) :
    transport G H e n a = k ≫ transport G H e m a := by
  change n a ≫ e.hom.hom.hom.hom = k ≫ m a ≫ e.hom.hom.hom.hom
  rw [hn, Category.assoc]

end FLT.Mazur.GroupMarkingTransport
