/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicCharacteristicChartSaturatedOpen
public import FLT.Mazur.CyclicCharacteristicInvariantAffineSaturation

/-!
# A finite quotient open cover from the original invariant affine charts

The full orbit images of the original affine cover are genuine compact opens.
This constructs the quotient domains without claiming that their sheaves are affine.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
namespace FLT.Mazur.CyclicCharacteristicOrbit
open CyclicCharacteristicAtlas
variable (n : ℕ) [NeZero n]

/-- The actual quotient image of an original invariant affine parameter chart. -/
def affineOrbitOpen (i : InvariantAffineIndex n) : Opens (Orbit n) :=
  chartDescendOpen n i.1 (invariantAffineInclusion n i).opensRange
    (invariantAffineInclusion_open_saturated n i)

/-- The quotient chart stays in its original characteristic locus. -/
theorem affineOrbitOpen_le (i : InvariantAffineIndex n) :
    affineOrbitOpen n i ≤ integerOpen n (chartInteger i.1) :=
  chartDescendOpen_le n i.1 _ _

/-- No extra normalized points appear in the preimage of this quotient open. -/
theorem affineOrbitOpen_preimage (i : InvariantAffineIndex n) :
    chartProjection n i.1 ⁻¹' (affineOrbitOpen n i : Set _) =
      Set.range (invariantAffineInclusion n i) :=
  chartProjection_preimage_image_of_saturated n i.1 _
    (invariantAffineInclusion_open_saturated n i)

/-- The quotient domain is exactly the image of the original affine parameter scheme. -/
theorem affineOrbitOpen_range (i : InvariantAffineIndex n) :
    Set.range (chartProjection n i.1 ∘ invariantAffineInclusion n i) =
      (affineOrbitOpen n i : Set _) :=
  Set.range_comp _ _

/-- The actual affine source makes each descended quotient open compact. -/
theorem affineOrbitOpen_isCompact (i : InvariantAffineIndex n) :
    IsCompact (affineOrbitOpen n i : Set (Orbit n)) := by
  rw [← affineOrbitOpen_range]
  exact isCompact_range ((chartProjection_continuous n i.1).comp
    (invariantAffineInclusion n i).continuous)

/-- The finite family of descended affine-source opens covers the full assembled orbit space. -/
theorem affineOrbitOpen_covers (z : Orbit n) :
    ∃ i : InvariantAffineIndex n, z ∈ affineOrbitOpen n i := by
  obtain ⟨x, rfl⟩ := projection_surjective n z
  obtain ⟨b, y, rfl⟩ := normalizedDisjointSource_covers n x
  obtain ⟨i, hi⟩ := invariantAffineCover_covers n b y
  exact ⟨⟨b, i⟩, y, hi, rfl⟩

/-- The descended domains form an actual open cover, retaining both characteristics. -/
theorem affineOrbitOpen_iSup : ⨆ i, affineOrbitOpen n i = ⊤ := by
  apply top_unique
  intro z _
  obtain ⟨i, hi⟩ := affineOrbitOpen_covers n z
  exact Opens.mem_iSup.mpr ⟨i, hi⟩

end FLT.Mazur.CyclicCharacteristicOrbit
