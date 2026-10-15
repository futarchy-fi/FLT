/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PartialEnvelopeFullFiber
public import Mathlib.AlgebraicGeometry.Morphisms.Proper

/-!
# Full interiors from partial proper charts

Properness is required only for the chart projections to the source. Their
images need cover only the complement of the chosen envelope open. Finite
subcover extraction handles arbitrary open families over a compact bad locus.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.SchemeOpenEnvelope
universe u v
variable {X Y : Scheme.{u}} (π : Y ⟶ X)
  {I : Type v} (E : I → Scheme.{u}) (g : ∀ i, E i ⟶ Y) (U : Y.Opens)
  (hg : ∀ y : Y, y ∉ U → ∃ i, ∃ z : E i, g i z = y)

include hg

/-- Closed chart projections suffice even when the ambient projection is not closed. -/
theorem isOpen_fullFiber_of_partialClosedCover [Finite I]
    (hc : ∀ i, IsClosedMap (g i ≫ π)) : IsOpen (fullFiberLocus π U) := by
  rw [fullFiberLocus_partialCover π E g U hg]
  exact isOpen_iInter_of_finite fun i ↦ (fullFiberOpen (g i ≫ π) (g i ⁻¹ᵁ U) (hc i)).isOpen

/-- Proper chart projections supply the closedness needed for arbitrary envelope opens. -/
theorem isOpen_fullFiber_of_partialProperCover [Finite I]
    [∀ i, IsProper (g i ≫ π)] : IsOpen (fullFiberLocus π U) :=
  isOpen_fullFiber_of_partialClosedCover π E g U hg fun i ↦ (g i ≫ π).isClosedMap

/-- Compactness reduces an infinite partial open family with closed projections to a finite one. -/
theorem isOpen_fullFiber_of_compact_partialClosedCover
    (hU : IsCompact (U : Set Y)ᶜ) (ho : ∀ i, IsOpen (Set.range (g i)))
    (hc : ∀ i, IsClosedMap (g i ≫ π)) : IsOpen (fullFiberLocus π U) := by
  obtain ⟨J, hJ⟩ := exists_finite_partialCover E g U hU ho hg
  apply isOpen_fullFiber_of_partialClosedCover π (fun i : J ↦ E i.val)
    (fun i ↦ g i.val) U ?_ (fun i ↦ hc i.val)
  intro y hy
  obtain ⟨i, hi, z, hz⟩ := hJ y hy
  exact ⟨⟨i, hi⟩, z, hz⟩

/-- Every original full fiber is retained in the actual maximal source open. -/
theorem fullInterior_eq_of_compact_partialClosedCover
    (hU : IsCompact (U : Set Y)ᶜ) (ho : ∀ i, IsOpen (Set.range (g i)))
    (hc : ∀ i, IsClosedMap (g i ≫ π)) :
    (fullFiberInterior π U : Set X) = fullFiberLocus π U :=
  (isOpen_fullFiber_of_compact_partialClosedCover π E g U hg hU ho hc).interior_eq

/-- A finite collection of full fibers has an actual original source denominator. -/
theorem exists_denominator_of_compact_partialClosedCover [IsAffine X]
    (hU : IsCompact (U : Set Y)ᶜ) (ho : ∀ i, IsOpen (Set.range (g i)))
    (hc : ∀ i, IsClosedMap (g i ≫ π)) (F : Set X) (hF : F.Finite)
    (hFU : F ⊆ fullFiberLocus π U) :
    ∃ r : Γ(X, ⊤), F ⊆ X.basicOpen r ∧ r ∈ denominatorIdeal π.appTop.hom U := by
  apply exists_fullFiberInterior_coefficient π U F hF
  rwa [fullInterior_eq_of_compact_partialClosedCover π E g U hg hU ho hc]

end FLT.Mazur.SchemeOpenEnvelope
