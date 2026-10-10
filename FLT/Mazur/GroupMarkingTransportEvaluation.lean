/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GroupMarkingTransport

/-!
# Evaluate an identified transported marking without unfolding its group

First identify the whole marking homomorphism. This lemma then evaluates
its sections with the concrete group structures kept behind that equality.
-/

@[expose] public noncomputable section

open CategoryTheory MonObj

namespace FLT.Mazur.GroupMarkingTransport

universe u v w
variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]
  [BraidedCategory C] {L : Type w} [Monoid L]
  (G H : CommGrp C) (e : G ≅ H) {T : C}

/-- Evaluate a full marking once its transport has been identified as a homomorphism. -/
theorem identified_apply (m : L →* (T ⟶ G.X)) (n : L →* (T ⟶ H.X))
    (hn : n = transport G H e m) (a : L) : n a = m a ≫ e.hom.hom.hom.hom := by
  rw [hn, transport_apply]

end FLT.Mazur.GroupMarkingTransport
