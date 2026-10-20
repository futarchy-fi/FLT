/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicCharacteristicOrbitResidualHomeomorphism
public import FLT.Mazur.CyclicCharacteristicAffineResidualPrincipal

/-!
# Actual residual principal neighborhoods form a basis

The proved topology comparison transports the spectrum basis to the original
orbit open. Its locally ringed comparison retains exactly this homeomorphism.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
namespace FLT.Mazur.CyclicCharacteristicOrbit
open CyclicCharacteristicAtlas
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (n : ℕ) [NeZero n] (i : InvariantAffineIndex n)

/-- Full residual principal domains are a topological basis on the actual orbit open. -/
theorem affineResidualPrincipal_isTopologicalBasis :
    IsTopologicalBasis (Set.range fun s : affineResidualSections n i =>
      (affineResidualPrincipal n i s : Set (affineOrbitOpen n i))) := by
  have h := (orbitToResidualSpectrum_isHomeomorph n i).isInducing.isTopologicalBasis
    (PrimeSpectrum.isTopologicalBasis_basic_opens (R := affineResidualSections n i))
  rw [← Set.range_comp] at h
  exact h

/-- The same principal domains are a basis in the lattice of actual opens. -/
theorem affineResidualPrincipal_isBasis :
    Opens.IsBasis (Set.range (affineResidualPrincipal n i)) := by
  unfold Opens.IsBasis
  rw [← Set.range_comp]
  exact affineResidualPrincipal_isTopologicalBasis n i

/-- Every original open neighborhood contains an original residual principal neighborhood. -/
theorem exists_affineResidualPrincipal_subset (V : Opens (affineOrbitOpen n i))
    (z : affineOrbitOpen n i) (hz : z ∈ V) :
    ∃ s : affineResidualSections n i, z ∈ affineResidualPrincipal n i s ∧
      affineResidualPrincipal n i s ≤ V := by
  obtain ⟨_, ⟨s, rfl⟩, hs, hsub⟩ :=
    (affineResidualPrincipal_isTopologicalBasis n i).exists_subset_of_mem_open hz V.isOpen
  exact ⟨s, hs, hsub⟩

/-- The constructed locally ringed comparison has a homeomorphism as its original base map. -/
theorem affineResidualRingedComparison_base_isHomeomorph :
    IsHomeomorph (affineResidualRingedComparison n i).base := by
  have he : ⇑(affineResidualRingedComparison n i).base = orbitToResidualSpectrum n i :=
    funext (affineResidualRingedComparison_base n i)
  rw [he]
  exact orbitToResidualSpectrum_isHomeomorph n i

end FLT.Mazur.CyclicCharacteristicOrbit
