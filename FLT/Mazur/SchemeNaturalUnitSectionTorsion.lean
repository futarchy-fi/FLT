/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeNaturalUnitLocus
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact

/-!
# Degree-power torsion from vanishing on the unit-degree locus

On a quasi-compact scheme, exact vanishing on the degree's principal open
is annihilated by one power of the original degree in global sections.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
namespace FLT.Mazur.SchemeNaturalUnitLocus
set_option backward.isDefEq.respectTransparency false
variable (X : Scheme.{0}) [CompactSpace X] (n : ℕ)

/-- Exact vanishing where the degree is invertible gives global degree-power torsion. -/
theorem exists_pow_mul_eq_zero (a : Γ(X, ⊤))
    (h : (locus X n).ι.appTop a = 0) : ∃ k : ℕ, (n : Γ(X, ⊤)) ^ k * a = 0 := by
  apply exists_pow_mul_eq_zero_of_res_basicOpen_eq_zero_of_isCompact
    X isCompact_univ a (n : Γ(X, ⊤))
  have he := congrArg (fun z => (locus X n).topIso.hom z) h
  rw [map_zero] at he
  change (X.presheaf.map _ ≫ X.presheaf.map _) a = 0 at he
  rw [← X.presheaf.map_comp] at he
  exact he

end FLT.Mazur.SchemeNaturalUnitLocus
