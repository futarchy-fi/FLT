/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.PolygonArithmeticStageProper
public import FLT.Mazur.PolygonArithmeticSystem
public import FLT.Mazur.PolygonInfinitesimalStageDivisor

/-!
# The full Cartier boundary on the arithmetic system

The product of the original unit-one section ideals is relative Cartier,
flat, and compatible with every arithmetic transition and with integral
specialization. Over a local ring with principal maximal ideal it is finite.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.PolygonArithmeticStages
open FCurve
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable (A : Type u) [CommRing A] (π : A) (m n : ℕ) (h : 2 ≤ n)

/-- The complete boundary product, with the unchanged unit-one marking on every component. -/
def boundaryIdeal : (family A π m n h).left.IdealSheafData :=
  PolygonInfinitesimal.markingDivisor (Quotient A π m) (parameter A π m) n h (fun _ ↦ 1)

/-- The actual arithmetic boundary is a relative effective Cartier divisor. -/
theorem boundaryIdeal_cartier :
    RelativeEffectiveCartier (family A π m n h).hom (boundaryIdeal A π m n h) :=
  PolygonInfinitesimal.markingDivisor_cartier _ _ n h _

/-- The entire boundary is flat over its original arithmetic coefficient ring. -/
instance boundaryIdeal_flat :
    Flat ((boundaryIdeal A π m n h).subschemeι ≫ (family A π m n h).hom) :=
  (boundaryIdeal_cartier A π m n h).2

/-- The boundary contains exactly the original labeled sections. -/
theorem boundaryIdeal_mem_support (x : (family A π m n h).left) :
    x ∈ (boundaryIdeal A π m n h).support ↔
      ∃ i, x ∈ Set.range (marking A π m n h i) :=
  PolygonInfinitesimal.markingDivisor_mem_support _ _ n h _ x

/-- Adjacent arithmetic restrictions retain the full Cartier ideal, not only its support. -/
theorem boundaryIdeal_stageRestriction :
    (boundaryIdeal A π (m + 1) n h).comap (stageRestriction A π m n h) =
      boundaryIdeal A π m n h :=
  section_prod_comap_of_cartesian (stageRestriction_isPullback A π m n h) Finset.univ _ _
    (fun i ↦ marking_base A π m n h i) (fun i ↦ marking_base A π (m + 1) n h i)
    (fun i ↦ marking_stageRestriction A π m n h i)

/-- Every transition of the original arithmetic system preserves the boundary ideal. -/
theorem boundaryIdeal_systemMap {a b : ℕ} (f : a ⟶ b) :
    (boundaryIdeal A π b n h).comap ((stageSystem A π n h).map f) =
      boundaryIdeal A π a n h := by
  have H : IsPullback ((stageSystem A π n h).map f) (family A π a n h).hom
      (family A π b n h).hom ((baseSystem A π).map f) :=
    systemStructure_equifibered A π n h f
  exact section_prod_comap_of_cartesian (f := (family A π a n h).hom)
    (g := (family A π b n h).hom) H Finset.univ _ _
    (fun i ↦ marking_base A π a n h i) (fun i ↦ marking_base A π b n h i)
    (fun i ↦ ((systemMarking A π n h i).naturality f).symm)

/-- Integral coefficient specialization retains the original universal boundary product. -/
theorem boundaryIdeal_specializationFamily :
    (PolygonInfinitesimalStages.boundaryIdeal A m n h).comap
        (specializationFamily A π m n h) = boundaryIdeal A π m n h := by
  simpa only [boundaryIdeal, PolygonInfinitesimalStages.boundaryIdeal, specializationFamily,
    map_one] using PolygonInfinitesimal.markingDivisor_parameterProjection
      (PolygonInfinitesimalStages.parameter A m) n h (specialization A π m).toRingHom
      (parameter A π m) (specialization_parameter A π m) (fun _ ↦ 1)

variable [IsLocalRing A]

/-- Properness of the arithmetic stage makes its full original boundary finite. -/
theorem boundaryIdeal_finite (hgen : IsLocalRing.maximalIdeal A = ideal A π) :
    IsFinite ((boundaryIdeal A π m n h).subschemeι ≫ (family A π m n h).hom) := by
  let _ := family_proper A π hgen m n h
  exact isFinite_section_prod _ Finset.univ (marking A π m n h)
    (fun i _ ↦ marking_base A π m n h i)

end FLT.Mazur.PolygonArithmeticStages
