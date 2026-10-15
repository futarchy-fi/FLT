/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ProperNeighborhoodAtlas

/-!
# Full interiors from constructed proper neighborhoods of excluded points

No chart family is input. Proper neighborhoods of the excluded envelope
points give a canonical family, and compactness constructs a finite partial
cover. The ambient projection itself need not be proper.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.SchemeOpenEnvelope
universe u
variable {X Y : Scheme.{u}} (π : Y ⟶ X) (U : Y.Opens)
  (hU : IsCompact (U : Set Y)ᶜ)
  (hproper : (U : Set Y)ᶜ ⊆ ProperNeighborhoodAtlas.locus π)

include hU hproper

/-- Construct finitely many actual proper charts covering every excluded envelope point. -/
theorem exists_properNeighborhood_partialCover :
    ∃ J : Finset (ProperNeighborhoodAtlas.Index π), ∀ y : Y, y ∉ U →
      ∃ i ∈ J, ∃ z : ProperNeighborhoodAtlas.source π i,
        ProperNeighborhoodAtlas.inclusion π i z = y :=
  ProperNeighborhoodAtlas.exists_finite_cover π _ hU hproper

/-- Proper neighborhoods of bad points construct openness without a supplied chart atlas. -/
theorem isOpen_fullFiber_of_properNeighborhoods : IsOpen (fullFiberLocus π U) := by
  obtain ⟨J, hJ⟩ := exists_properNeighborhood_partialCover π U hU hproper
  apply isOpen_fullFiber_of_partialProperCover π
    (fun i : J ↦ ProperNeighborhoodAtlas.source π i.val)
    (fun i ↦ ProperNeighborhoodAtlas.inclusion π i.val) U
  intro y hy
  obtain ⟨i, hi, z, hz⟩ := hJ y hy
  exact ⟨⟨i, hi⟩, z, hz⟩

/-- All original full fibers belong to the actual maximal open under this local geometry. -/
theorem fullInterior_eq_of_properNeighborhoods :
    (fullFiberInterior π U : Set X) = fullFiberLocus π U :=
  (isOpen_fullFiber_of_properNeighborhoods π U hU hproper).interior_eq

/-- Finite collections of full fibers obtain actual source denominators from the atlas. -/
theorem exists_denominator_of_properNeighborhoods [IsAffine X]
    (F : Set X) (hF : F.Finite) (hFU : F ⊆ fullFiberLocus π U) :
    ∃ r : Γ(X, ⊤), F ⊆ X.basicOpen r ∧ r ∈ denominatorIdeal π.appTop.hom U := by
  apply exists_fullFiberInterior_coefficient π U F hF
  rwa [fullInterior_eq_of_properNeighborhoods π U hU hproper]

omit hU in
/-- Affine envelopes supply compactness for every open, with no noetherian hypothesis. -/
theorem isOpen_fullFiber_of_affine_properNeighborhoods [IsAffine Y] :
    IsOpen (fullFiberLocus π U) :=
  isOpen_fullFiber_of_properNeighborhoods π U U.isOpen.isClosed_compl.isCompact hproper

end FLT.Mazur.SchemeOpenEnvelope
