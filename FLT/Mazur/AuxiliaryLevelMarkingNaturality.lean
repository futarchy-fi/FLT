/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AuxiliaryLevelHomScheme

/-!
# Naturality of the scheme representing a complete marking

A natural family of group-valued sections represents a natural family of
actual scheme morphisms to the original marking equation scheme.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry MonObj

namespace FLT.Mazur.AuxiliaryLevel

variable {S : Scheme} (E : Over S) [GrpObj E] (A : Type) [Group A] [Fintype A]
  {U V : Over S}

/-- Representing a complete marking commutes with every change of test scheme. -/
theorem liftMarking_natural (k : U ⟶ V) (m : A →* (V ⟶ E)) (n : A →* (U ⟶ E))
    (hn : ∀ a, n a = k ≫ m a) : liftMarking E A n = k ≫ liftMarking E A m := by
  apply homScheme_ext
  intro a
  rw [Category.assoc, liftMarking_value, liftMarking_value]
  exact hn a

end FLT.Mazur.AuxiliaryLevel
