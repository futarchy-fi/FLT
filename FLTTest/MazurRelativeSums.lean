/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

import FLT.Mazur.RelativeSums

/-! # Axiom checks for relative Cartier sums

The flatness and base-change arguments must not depend on arithmetic assumptions.
-/

/-- info: 'FLT.Mazur.FCurve.flat_quotient_mul'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FLT.Mazur.FCurve.flat_quotient_mul

/-- info: 'FLT.Mazur.FCurve.relativeCartierSum'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FLT.Mazur.FCurve.relativeCartierSum

/-- info: 'FLT.Mazur.FCurve.smoothOpen_section_prod_baseChange'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FLT.Mazur.FCurve.smoothOpen_section_prod_baseChange

/-- info: 'FLT.Mazur.FCurve.section_prod_comap_eq'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FLT.Mazur.FCurve.section_prod_comap_eq

open CategoryTheory AlgebraicGeometry FLT.Mazur.FCurve

-- A doubled section is allowed; pairwise disjointness is not an assumption.
example {U X S : Scheme} (j : U ⟶ X) (f : X ⟶ S) (s : S ⟶ U)
    [IsOpenImmersion j] [SmoothOfRelativeDimension 1 (j ≫ f)] [IsSeparated f]
    (hs : s ≫ j ≫ f = 𝟙 S) :
    RelativeEffectiveCartier f ((s ≫ j).ker ^ 2) :=
  (smoothOpenSectionCartier j f s inferInstance inferInstance inferInstance hs).pow 2

-- The empty family gives the unit ideal over an arbitrary ambient family.
example {X S : Scheme} (f : X ⟶ S) :
    RelativeEffectiveCartier f (∏ _i ∈ (∅ : Finset ℕ), (⊤ : X.IdealSheafData)) := by
  simpa using relativeEffectiveCartier_prod f (∅ : Finset ℕ)
    (fun _ ↦ (⊤ : X.IdealSheafData)) (by simp)
