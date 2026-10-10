/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonInfinitesimalDivisor
public import FLT.Mazur.PolygonInfinitesimalStageProper
public import FLT.Mazur.PolygonInfinitesimalSystem

/-!
# The finite flat Cartier divisor throughout the concrete smoothing system

At every order the unit-one markings give a relative Cartier sum. The whole
ideal, including its multiplicities, is compatible with every transition of
the actual system. Over a field its closed subscheme is finite and flat.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace FLT.Mazur.PolygonInfinitesimalStages

open FCurve

variable (R : Type u) [CommRing R] (m n : ℕ) (h : 2 ≤ n)

/-- The unit-one Cartier sum on the concrete stage. -/
def boundaryIdeal : (family R m n h).left.IdealSheafData :=
  PolygonInfinitesimal.markingDivisor (Ring R m) (parameter R m) n h (fun _ ↦ 1)

/-- The full stage boundary is relative effective Cartier. -/
theorem boundaryIdeal_cartier :
    RelativeEffectiveCartier (family R m n h).hom (boundaryIdeal R m n h) :=
  PolygonInfinitesimal.markingDivisor_cartier _ _ n h _

/-- Adjacent coefficient restriction retains the entire Cartier divisor ideal. -/
theorem boundaryIdeal_stageRestriction :
    (boundaryIdeal R (m + 1) n h).comap (stageRestriction R m n h) =
      boundaryIdeal R m n h :=
  section_prod_comap_of_cartesian (stageRestriction_isPullback R m n h) Finset.univ _ _
    (fun i ↦ marking_base R m n h i) (fun i ↦ marking_base R (m + 1) n h i)
    (fun i ↦ marking_stageRestriction R m n h i)

/-- Every transition, not just adjacent ones, retains the actual boundary divisor. -/
theorem boundaryIdeal_systemMap {a b : ℕ} (f : a ⟶ b) :
    (boundaryIdeal R b n h).comap ((stageSystem R n h).map f) = boundaryIdeal R a n h := by
  let _ : IsSeparated (family R b n h).hom := family_separated R b n h
  have H : IsPullback ((stageSystem R n h).map f) (family R a n h).hom
      (family R b n h).hom ((baseSystem R).map f) :=
    (systemStructure_equifibered R n h) f
  exact section_prod_comap_of_cartesian (f := (family R a n h).hom)
    (g := (family R b n h).hom) H Finset.univ _ _
    (fun i ↦ marking_base R a n h i) (fun i ↦ marking_base R b n h i)
    (fun i ↦ ((systemMarking R n h i).naturality f).symm)

/-- The closed boundary family is flat over the original truncated coefficient ring. -/
instance boundaryIdeal_flat : Flat ((boundaryIdeal R m n h).subschemeι ≫ (family R m n h).hom) :=
  (boundaryIdeal_cartier R m n h).2

variable (K : Type u) [Field K]

/-- Properness makes the full marked boundary finite over the truncated field base. -/
instance boundaryIdeal_finite :
    IsFinite ((boundaryIdeal K m n h).subschemeι ≫ (family K m n h).hom) :=
  isFinite_section_prod _ Finset.univ (marking K m n h) (fun i _ ↦ marking_base K m n h i)

end FLT.Mazur.PolygonInfinitesimalStages
