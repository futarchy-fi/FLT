/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.AlgebraicGeometry.AffineScheme

/-!
# Principal neighborhoods from the original scalar ring

For a map from an original scalar ring to scheme coordinates, the complement
of the closure of the bad image is exactly the locus admitting an original
principal neighborhood inside a prescribed open. For a closed scalar map,
containment of the whole fiber suffices. A single point of the fiber does not.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.SchemeScalarPrincipalNeighborhood
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R] {X : Scheme} (s : R →+* Γ(X, ⊤))

/-- The scheme map induced by the original scalar ring, without changing that ring. -/
def scalarMorphism : X ⟶ Spec (.of R) :=
  X.toSpecΓ ≫ Spec.map (CommRingCat.ofHom s)

/-- Original principal opens pull back to the specified scalar functions. -/
theorem scalarMorphism_preimage (r : R) :
    scalarMorphism s ⁻¹ᵁ PrimeSpectrum.basicOpen r = X.basicOpen (s r) := by
  change X.toSpecΓ ⁻¹ᵁ PrimeSpectrum.basicOpen (s r) = _
  exact X.toSpecΓ_preimage_basicOpen (s r)

/-- The exact open locus where an original scalar can avoid the entire bad target. -/
def scalarNeighborhoodLocus (O : X.Opens) : (Spec (.of R)).Opens :=
  ⟨(closure (scalarMorphism s '' (O : Set X)ᶜ))ᶜ, isClosed_closure.isOpen_compl⟩

/-- Membership constructs a scalar outside the original prime, with the required containment. -/
theorem mem_scalarNeighborhoodLocus_iff (O : X.Opens) (P : PrimeSpectrum R) :
    P ∈ scalarNeighborhoodLocus s O ↔
      ∃ r : R, r ∉ P.asIdeal ∧ X.basicOpen (s r) ≤ O := by
  constructor
  · intro hP
    obtain ⟨_, ⟨r, rfl⟩, hrP, hr⟩ :=
      PrimeSpectrum.isTopologicalBasis_basic_opens.isOpen_iff.mp
        (scalarNeighborhoodLocus s O).isOpen P hP
    refine ⟨r, hrP, ?_⟩
    intro x hx
    by_contra hxo
    have hx' : scalarMorphism s x ∈ PrimeSpectrum.basicOpen r := by
      change x ∈ scalarMorphism s ⁻¹ᵁ PrimeSpectrum.basicOpen r
      rwa [scalarMorphism_preimage]
    exact hr hx' (subset_closure ⟨x, hxo, rfl⟩)
  · rintro ⟨r, hrP, hr⟩
    change P ∉ closure (scalarMorphism s '' (O : Set X)ᶜ)
    have hsub : scalarMorphism s '' (O : Set X)ᶜ ⊆
        (PrimeSpectrum.basicOpen r : Set (PrimeSpectrum R))ᶜ := by
      rintro y ⟨x, hx, rfl⟩ hy
      apply hx
      apply hr
      rw [← scalarMorphism_preimage]
      exact hy
    intro hP
    exact closure_minimal hsub (PrimeSpectrum.basicOpen r).isOpen.isClosed_compl hP hrP

/-- For closed scalar maps it suffices that every point over the prime lies in the open. -/
theorem exists_scalar_of_closed_fiber (O : X.Opens) (P : PrimeSpectrum R)
    (hs : IsClosedMap (scalarMorphism s))
    (hP : ∀ x : X, scalarMorphism s x = P → x ∈ O) :
    ∃ r : R, r ∉ P.asIdeal ∧ X.basicOpen (s r) ≤ O := by
  apply (mem_scalarNeighborhoodLocus_iff s O P).mp
  change P ∉ closure (scalarMorphism s '' (O : Set X)ᶜ)
  rw [(hs _ O.isOpen.isClosed_compl).closure_eq]
  rintro ⟨x, hx, he⟩
  exact hx (hP x he)

end FLT.Mazur.SchemeScalarPrincipalNeighborhood
