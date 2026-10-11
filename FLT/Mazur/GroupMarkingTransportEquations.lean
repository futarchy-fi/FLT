/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GroupMarkingTransport

/-!
# Equations for complete group markings without expanding geometric group laws

The cancellation and torsion equations are proved for abstract group objects.
They can then be specialized to concrete geometric comparisons while keeping
large scheme and group-law constructions sealed during kernel checking.
-/

@[expose] public noncomputable section
open CategoryTheory MonObj
namespace FLT.Mazur.GroupMarkingTransport
universe u v w
variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]
  [BraidedCategory C] {L : Type w} [Monoid L]
  (G H : CommGrp C) (e : G ≅ H) {T : C}

/-- Comparing a transported marking back to its original group retains every label. -/
theorem transport_compare (m : L →* (T ⟶ G.X)) (a : L) :
    transport G H e m a ≫ e.inv.hom.hom.hom = m a :=
  DFunLike.congr_fun (transport_symm_transport G H e m) a

/-- Any finite-order label retains its power equation in a marked group object. -/
theorem marking_pow_eq_one (m : L →* (T ⟶ G.X)) (a : L) (n : ℕ) (ha : a ^ n = 1) :
    m a ^ n = 1 := by
  rw [← map_pow, ha, map_one]

end FLT.Mazur.GroupMarkingTransport
