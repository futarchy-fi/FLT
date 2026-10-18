/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EquivalenceRelationCompleteTestFinite
public import FLT.Mazur.EquivalenceRelationCompleteThickenings

/-!
# Finite original projections at every complete infinitesimal order

Every constructed complete thickening makes the entire original first
projection finite after base change. Every original point has such a test at
every order. These closed tests do not imply ambient finite neighborhoods.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationNormalizedFrames
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D A : Scheme.{0}} {p q : D ⟶ A} [IsSeparated p] [Etale p]
  (I : Type) [Fintype I] (o : I)
attribute [local irreducible] source first completeThickening completeThickeningInclusion

/-- Finiteness holds over the full original complete thickening at every order. -/
theorem completeThickening_original_finite (k : ℕ) :
    IsFinite (pullback.snd p (completeThickeningInclusion I o k ≫ first p q I o)) :=
  original_pullback_finite_of_complete I o (completeThickeningInclusion I o k)
    (completeThickeningInclusion_range I o k).le

/-- Arbitrary tests on a complete thickening also have finite whole original pullbacks. -/
theorem completeThickening_test_original_finite (k : ℕ) {T : Scheme}
    (a : T ⟶ completeThickening (p := p) (q := q) I o k) :
    IsFinite (pullback.snd p
      ((a ≫ completeThickeningInclusion I o k) ≫ first p q I o)) := by
  apply original_pullback_finite_of_complete
  rintro _ ⟨x, rfl⟩
  exact (completeThickeningInclusion_range I o k).le (Set.mem_range_self (a x))

variable [QuasiCompact p] (e : CategoryTheory.EquivalenceRelation p q)

include e in
/-- Every original point admits a finite whole-relation test at each infinitesimal order. -/
theorem exists_completeThickening_finite_lift (x : A) (k : ℕ) :
    ∃ (n : ℕ) (j : Fin n) (y : completeThickening (p := p) (q := q) (Fin n) j k),
      (completeThickeningInclusion (Fin n) j k ≫ first p q (Fin n) j) y = x ∧
      IsFinite (pullback.snd p
        (completeThickeningInclusion (Fin n) j k ≫ first p q (Fin n) j)) := by
  obtain ⟨n, j, y, hy⟩ := exists_completeThickening_lift e x k
  exact ⟨n, j, y, hy, completeThickening_original_finite (Fin n) j k⟩

end FLT.Mazur.EquivalenceRelationNormalizedFrames
