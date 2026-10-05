/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteIntersectionSectionComparison
public import FLT.Mazur.ModuleSheafUnitCocycle

/-!
# Transition units in the finite intersection coordinate diagram

Ordered pairs of labels in an intersection index its transition units.
Inclusion of label sets carries these pairs forward, and ordered triples
index the multiplication laws needed for finite coefficient descent.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry
open FLT.Mazur.FCurve.ModuleSheafUnitCocycle

namespace FLT.Mazur.Approximation

universe u

/-- Ordered chart pairs present in a finite intersection. -/
abbrev IntersectionPair {ι : Type u} (s : NonemptyChartSet ι) :=
  {i // i ∈ s.val} × {i // i ∈ s.val}

/-- Ordered chart triples present in a finite intersection. -/
abbrev IntersectionTriple {ι : Type u} (s : NonemptyChartSet ι) :=
  {i // i ∈ s.val} × {i // i ∈ s.val} × {i // i ∈ s.val}

/-- Inclusion of label sets preserves an ordered pair. -/
def intersectionPairMap {ι : Type u} {s t : NonemptyChartSet ι} (f : s ⟶ t)
    (k : IntersectionPair s) : IntersectionPair t :=
  (⟨k.1.val, leOfHom f k.1.property⟩, ⟨k.2.val, leOfHom f k.2.property⟩)

variable {A : Type u} [CommRing A] {X : Scheme.{u}} {ι : Type u}
  (U : ι → X.Opens) (p : X ⟶ Spec (.of A)) (g : Cocycle U)

/-- Every intersection lies in each of its member charts. -/
theorem finiteIntersectionOpen_le_chart (s : NonemptyChartSet ι) (i : {i // i ∈ s.val}) :
    finiteIntersectionOpen U s ≤ U i.val :=
  iInf_le_of_le i.val (iInf_le _ i.property)

/-- The actual transition unit expressed in the coordinate algebra. -/
def finiteIntersectionCocycleUnit (s : NonemptyChartSet ι) (k : IntersectionPair s) :
    ((finiteIntersectionSectionDiagram U p).obj s)ˣ :=
  Units.map (finiteIntersectionSectionEquiv U p s).toMonoidHom
    (g.unit k.1.val k.2.val (finiteIntersectionOpen U s)
      (finiteIntersectionOpen_le_chart U s k.1) (finiteIntersectionOpen_le_chart U s k.2))

/-- Coordinate transition units commute with the diagram restrictions. -/
theorem finiteIntersectionCocycleUnit_naturality {s t : NonemptyChartSet ι}
    (f : s ⟶ t) (k : IntersectionPair s) :
    ((finiteIntersectionSectionDiagram U p).map f).hom
        (finiteIntersectionCocycleUnit U p g s k) =
      (finiteIntersectionCocycleUnit U p g t (intersectionPairMap f k) :
        (finiteIntersectionSectionDiagram U p).obj t) := by
  change ((finiteIntersectionSectionDiagram U p).map f).hom
    (finiteIntersectionSectionEquiv U p s _) = finiteIntersectionSectionEquiv U p t _
  rw [finiteIntersectionSectionEquiv_naturality]
  congr 1
  exact g.natural _ _ _ _ _

/-- Triple labels give the multiplicative cocycle equations in one coordinate ring. -/
theorem finiteIntersectionCocycleUnit_mul (s : NonemptyChartSet ι)
    (k : IntersectionTriple s) :
    finiteIntersectionCocycleUnit U p g s (k.1, k.2.1) *
      finiteIntersectionCocycleUnit U p g s (k.2.1, k.2.2) =
        finiteIntersectionCocycleUnit U p g s (k.1, k.2.2) := by
  unfold finiteIntersectionCocycleUnit
  rw [← map_mul, g.cocycle]

/-- Diagonal coordinate transition units are one. -/
@[simp]
theorem finiteIntersectionCocycleUnit_self (s : NonemptyChartSet ι)
    (i : {i // i ∈ s.val}) : finiteIntersectionCocycleUnit U p g s (i, i) = 1 := by
  simp [finiteIntersectionCocycleUnit, g.refl]

end FLT.Mazur.Approximation
