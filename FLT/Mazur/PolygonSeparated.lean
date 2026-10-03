/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OneGonSeparated
public import FLT.Mazur.PolygonCyclicSeparated
public import FLT.Mazur.PolygonCoconeComparison
/-!
# Separatedness of every positive polygon

Combine the actual one-gon and cyclic atlas proofs and transport along the
canonical cocone comparison to any supplied pinching pushout.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace FLT.Mazur.PolygonSeparated
variable (K : Type u) [Field K]
/-- The specified polygon is separated for every positive size. -/
instance atlas (n : ℕ) [NeZero n] : (PolygonAtlas.polygon K n).left.IsSeparated := by
  rcases n with _ | (_ | n)
  · exact (NeZero.ne 0 rfl).elim
  · exact OneGonSeparated.scheme_separated K
  · exact PolygonCyclicSeparated.scheme_separated K (n + 2) (by omega)
open PolygonPinching
variable (n : ℕ) [NeZero n] (hn : 0 < n) {C : Over (Spec (.of K))}
  (p : components K n ⟶ C) (q : nodes K n ⟶ C)
  (h : IsPushout (toComponents K n hn) (toNodes K n) p q)
include h in
/-- Every specified pinching pushout has a separated underlying scheme. -/
theorem cocone : C.left.IsSeparated := by
  let e := (Over.forget (Spec (.of K))).mapIso (polygonIso K n hn p q h)
  constructor
  rw [← MorphismProperty.cancel_left_of_respectsIso @IsSeparated e.hom]
  rw [show e.hom ≫ terminal.from C.left = terminal.from (PolygonAtlas.polygon K n).left from
    terminal.hom_ext _ _]
  exact (atlas K n).isSeparated_terminal_from
end FLT.Mazur.PolygonSeparated
