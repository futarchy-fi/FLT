/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeOpenEnvelopeLocus

/-!
# Maximal open full-fiber domains without a closed projection

The interior of the full-fiber locus is the largest open whose entire
independent envelope is present. Open relation endpoints preserve it whenever
they preserve the full-fiber set. No closedness of the projection is needed.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.SchemeOpenEnvelope
universe u
variable {X Y : Scheme.{u}} (π : Y ⟶ X) (U : Y.Opens)

/-- The maximal open source supporting a full independent envelope. -/
def fullFiberInterior : X.Opens := ⟨interior (fullFiberLocus π U), isOpen_interior⟩

/-- Every point of the constructed open has its entire actual scheme fiber in the envelope. -/
theorem fullFiberInterior_subset : (fullFiberInterior π U : Set X) ⊆ fullFiberLocus π U :=
  interior_subset

/-- The independent envelope over the interior lies in the given open. -/
theorem preimage_fullFiberInterior_le : π ⁻¹ᵁ fullFiberInterior π U ≤ U :=
  (subset_fullFiberLocus_iff π U _).mp (fullFiberInterior_subset π U)

/-- This construction includes every open source with a full independent envelope. -/
theorem le_fullFiberInterior_iff (W : X.Opens) :
    W ≤ fullFiberInterior π U ↔ π ⁻¹ᵁ W ≤ U := by
  constructor
  · exact fun h y hy ↦ preimage_fullFiberInterior_le π U (h hy)
  · intro h
    exact interior_maximal ((subset_fullFiberLocus_iff π U W).mpr h) W.isOpen

/-- Enlarging the envelope enlarges the maximal open source. -/
theorem fullFiberInterior_mono {U V : Y.Opens} (h : U ≤ V) :
    fullFiberInterior π U ≤ fullFiberInterior π V :=
  (le_fullFiberInterior_iff π V _).mpr ((preimage_fullFiberInterior_le π U).trans h)

/-- A closed projection recovers the earlier full-fiber open exactly. -/
theorem fullFiberInterior_eq_fullFiberOpen (hπ : IsClosedMap π) :
    fullFiberInterior π U = fullFiberOpen π U hπ := by
  apply SetLike.coe_injective
  exact (fullFiberOpen π U hπ).isOpen.interior_eq

/-- Nonvanishing source coefficients detect membership in this maximal open domain. -/
theorem basicOpen_le_fullFiberInterior_iff (r : Γ(X, ⊤)) :
    X.basicOpen r ≤ fullFiberInterior π U ↔ r ∈ denominatorIdeal π.appTop.hom U := by
  rw [le_fullFiberInterior_iff, mem_denominatorIdeal, Scheme.Hom.preimage_basicOpen_top]

/-- Open continuous endpoints preserve the interior of an invariant full-fiber set. -/
theorem fullFiberInterior_invariant {Z : Scheme.{u}} (p q : Z ⟶ X)
    (hp : IsOpenMap p) (hq : IsOpenMap q)
    (h : p ⁻¹' fullFiberLocus π U = q ⁻¹' fullFiberLocus π U) :
    p ⁻¹ᵁ fullFiberInterior π U = q ⁻¹ᵁ fullFiberInterior π U := by
  apply SetLike.coe_injective
  change p ⁻¹' interior (fullFiberLocus π U) = q ⁻¹' interior (fullFiberLocus π U)
  rw [hp.preimage_interior_eq_interior_preimage p.continuous,
    hq.preimage_interior_eq_interior_preimage q.continuous, h]

/-- Any finite subset of the interior admits one actual nonvanishing source denominator. -/
theorem exists_fullFiberInterior_coefficient [IsAffine X]
    (s : Set X) (hs : s.Finite) (h : s ⊆ fullFiberInterior π U) :
    ∃ r : Γ(X, ⊤), s ⊆ X.basicOpen r ∧ r ∈ denominatorIdeal π.appTop.hom U := by
  obtain ⟨r, hr, hU⟩ := AffineEnvelopeFiniteNeighborhood.exists_envelope_principal
    (fullFiberInterior π U) s hs h
  exact ⟨r, hr, (basicOpen_le_fullFiberInterior_iff π U r).mp hU⟩

end FLT.Mazur.SchemeOpenEnvelope
