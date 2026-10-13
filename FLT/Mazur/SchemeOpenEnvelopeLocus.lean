/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeOpenEnvelopeDenominators
public import FLT.Mazur.AffineEnvelopeFiniteNeighborhood

/-!
# The source locus supporting an entire open envelope

Remove the image of the missing envelope. This constructs the largest source
set whose entire inverse image lies in the prescribed open. A closed projection
makes it open; on an affine source, prime avoidance then constructs nonvanishing
source coefficients. These coefficients are not asserted to be invariant.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.SchemeOpenEnvelope
universe u
variable {X Y : Scheme.{u}} (π : Y ⟶ X) (U : Y.Opens)

/-- The complement of the actual missing-envelope image in the original source. -/
def fullFiberLocus : Set X := (π '' (U : Set Y)ᶜ)ᶜ

/-- Membership tests every point of the actual scheme fiber, including residue-field branches. -/
theorem mem_fullFiberLocus (x : X) :
    x ∈ fullFiberLocus π U ↔ ∀ y : Y, π y = x → y ∈ U := by
  constructor
  · intro hx y hy
    by_contra h
    exact hx ⟨y, h, hy⟩
  · intro hx ⟨y, hy, he⟩
    exact hy (hx y he)

/-- The whole envelope over the constructed source locus lies in the original open. -/
theorem preimage_fullFiberLocus_le : π ⁻¹' fullFiberLocus π U ⊆ U := by
  intro y hy
  exact (mem_fullFiberLocus π U (π y)).mp hy y rfl

/-- The constructed locus is maximal among all sets supporting a full envelope. -/
theorem subset_fullFiberLocus_iff (S : Set X) :
    S ⊆ fullFiberLocus π U ↔ π ⁻¹' S ⊆ U := by
  constructor
  · exact fun h y hy ↦ preimage_fullFiberLocus_le π U (h hy)
  · intro h x hx
    apply (mem_fullFiberLocus π U x).mpr
    intro y hy
    apply h
    change π y ∈ S
    rwa [hy]

/-- Closedness of the projection makes the constructed full-fiber locus open. -/
def fullFiberOpen (hπ : IsClosedMap π) : X.Opens :=
  ⟨fullFiberLocus π U, (hπ _ U.isOpen.isClosed_compl).isOpen_compl⟩

/-- The inverse image of the constructed open fills the original envelope. -/
theorem preimage_fullFiberOpen_le (hπ : IsClosedMap π) :
    π ⁻¹ᵁ fullFiberOpen π U hπ ≤ U := preimage_fullFiberLocus_le π U

/-- Every nonvanishing coefficient supported in this open is an actual envelope denominator. -/
theorem basicOpen_le_fullFiberOpen_iff (hπ : IsClosedMap π) (r : Γ(X, ⊤)) :
    X.basicOpen r ≤ fullFiberOpen π U hπ ↔
      r ∈ denominatorIdeal π.appTop.hom U := by
  rw [mem_denominatorIdeal, ← Scheme.Hom.preimage_basicOpen_top]
  exact subset_fullFiberLocus_iff π U (X.basicOpen r)

/-- A finite set of full fibers constructs one source coefficient avoiding every chosen point. -/
theorem exists_fullFiber_coefficient [IsAffine X] (hπ : IsClosedMap π)
    (s : Set X) (hs : s.Finite) (hsU : s ⊆ fullFiberLocus π U) :
    ∃ r : Γ(X, ⊤), s ⊆ X.basicOpen r ∧ r ∈ denominatorIdeal π.appTop.hom U := by
  obtain ⟨r, hr, hU⟩ := AffineEnvelopeFiniteNeighborhood.exists_envelope_principal
    (fullFiberOpen π U hπ) s hs hsU
  exact ⟨r, hr, (basicOpen_le_fullFiberOpen_iff π U hπ r).mp hU⟩

/-- In particular a good fiber has a genuine nonvanishing source denominator. -/
theorem exists_fullFiber_coefficient_at [IsAffine X] (hπ : IsClosedMap π)
    (x : X) (hx : x ∈ fullFiberLocus π U) :
    ∃ r : Γ(X, ⊤), x ∈ X.basicOpen r ∧ r ∈ denominatorIdeal π.appTop.hom U := by
  obtain ⟨r, hr, hU⟩ := exists_fullFiber_coefficient π U hπ {x}
    (Set.finite_singleton x) (Set.singleton_subset_iff.mpr hx)
  exact ⟨r, hr (Set.mem_singleton x), hU⟩

end FLT.Mazur.SchemeOpenEnvelope
