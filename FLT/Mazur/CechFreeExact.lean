/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CechFreeStalkExactAll

/-!
# Exactness of the augmented free Cech complex

Exactness on stalks descends to sheaves in every degree, including the
constant integer term in degree zero.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace FLT.Mazur.CechFreeResolution

variable {X : TopCat.{u}} {ι : Type u} (U : ι → Opens X)

/-- The augmented free complex of an open cover is exact in every degree. -/
lemma freeAugmented_exactAt (hU : iSup U = ⊤) (n : ℕ) :
    (freeAugmented U).ExactAt n := by
  apply (TopCat.Sheaf.exact_iff_stalkFunctor_map_exact _).mpr
  intro x
  exact freeAugmented_stalk_exactAt U hU x n

end FLT.Mazur.CechFreeResolution
