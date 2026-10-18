/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeScalarPrincipalNeighborhood
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap

/-!
# Integral scalar maps and simultaneous independent neighborhoods

Integral coordinate maps supply the closedness needed to construct an
original scalar from whole-fiber containment. Finitely many independent
targets use one scalar outside the same original prime.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
namespace FLT.Mazur.SchemeScalarPrincipalNeighborhood
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R]

/-- Integrality over the original ring proves the scalar map is closed. -/
theorem scalarMorphism_isClosedMap {X : Scheme} [IsAffine X]
    (s : R →+* Γ(X, ⊤)) (hs : s.IsIntegral) : IsClosedMap (scalarMorphism s) := by
  exact (PrimeSpectrum.isClosedMap_comap_of_isIntegral s hs).comp X.toSpecΓ.homeomorph.isClosedMap

/-- Integral original scalars shrink around the whole specified original fiber. -/
theorem exists_scalar_of_integral_fiber {X : Scheme} [IsAffine X]
    (s : R →+* Γ(X, ⊤)) (hs : s.IsIntegral) (O : X.Opens) (P : PrimeSpectrum R)
    (hP : ∀ x : X, scalarMorphism s x = P → x ∈ O) :
    ∃ r : R, r ∉ P.asIdeal ∧ X.basicOpen (s r) ≤ O :=
  exists_scalar_of_closed_fiber s O P (scalarMorphism_isClosedMap s hs) hP

/-- One original scalar works simultaneously on finitely many independent scheme targets. -/
theorem exists_scalar_family {ι : Type} [Finite ι] (X : ι → Scheme)
    (s : ∀ a, R →+* Γ(X a, ⊤)) (O : ∀ a, (X a).Opens) (P : PrimeSpectrum R)
    (hP : ∀ a, P ∈ scalarNeighborhoodLocus (s a) (O a)) :
    ∃ r : R, r ∉ P.asIdeal ∧ ∀ a, (X a).basicOpen (s a r) ≤ O a := by
  let V : (Spec (.of R)).Opens := ⨅ a, scalarNeighborhoodLocus (s a) (O a)
  have hPV : P ∈ V := by
    change P ∈ (((⨅ a, scalarNeighborhoodLocus (s a) (O a)) : (Spec (.of R)).Opens) :
      Set (Spec (.of R)))
    rw [Opens.coe_iInf]
    exact Set.mem_iInter.mpr hP
  obtain ⟨_, ⟨r, rfl⟩, hrP, hr⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.isOpen_iff.mp V.isOpen P hPV
  refine ⟨r, hrP, ?_⟩
  intro a x hx
  by_contra hxo
  have hx' : scalarMorphism (s a) x ∈ PrimeSpectrum.basicOpen r := by
    change x ∈ scalarMorphism (s a) ⁻¹ᵁ PrimeSpectrum.basicOpen r
    rwa [scalarMorphism_preimage]
  have hz : scalarMorphism (s a) x ∈ scalarNeighborhoodLocus (s a) (O a) :=
    (iInf_le (fun a ↦ scalarNeighborhoodLocus (s a) (O a)) a) (hr hx')
  exact hz (subset_closure ⟨x, hxo, rfl⟩)

/-- Independent integral targets have a common original denominator from fiber containment. -/
theorem exists_scalar_family_of_integral {ι : Type} [Finite ι]
    (X : ι → Scheme) [∀ a, IsAffine (X a)]
    (s : ∀ a, R →+* Γ(X a, ⊤)) (hs : ∀ a, (s a).IsIntegral)
    (O : ∀ a, (X a).Opens) (P : PrimeSpectrum R)
    (hP : ∀ a (x : X a), scalarMorphism (s a) x = P → x ∈ O a) :
    ∃ r : R, r ∉ P.asIdeal ∧ ∀ a, (X a).basicOpen (s a r) ≤ O a := by
  apply exists_scalar_family X s O P
  intro a
  exact (mem_scalarNeighborhoodLocus_iff (s a) (O a) P).mpr
    (exists_scalar_of_integral_fiber (s a) (hs a) (O a) P (hP a))

end FLT.Mazur.SchemeScalarPrincipalNeighborhood
