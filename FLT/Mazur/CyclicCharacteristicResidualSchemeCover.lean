/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicCharacteristicOrbitScheme
public import Mathlib.AlgebraicGeometry.Gluing

/-!
# The full residual spectra cover the actual quotient scheme

The chart maps are the inverses of the original ringed comparisons followed by
the original orbit-open inclusions. Thus their overlaps are scheme overlaps.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.CyclicCharacteristicOrbit
open CyclicCharacteristicAtlas
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (n : ℕ) [NeZero n]

/-- The full residual chart maps into the actual orbit scheme by the original comparison. -/
def affineResidualInclusion (i : InvariantAffineIndex n) :
    affineResidualSpectrum n i ⟶ invariantOrbitScheme n :=
  (invariantOrbitAffineIso n i).inv ≫
    (show (invariantOrbitScheme n).Opens from affineOrbitOpen n i).ι

/-- These maps are genuine open immersions of schemes. -/
instance affineResidualInclusion_isOpenImmersion (i : InvariantAffineIndex n) :
    IsOpenImmersion (affineResidualInclusion n i) := by
  unfold affineResidualInclusion
  infer_instance

/-- The chart inclusion recovers every original point of the selected orbit open. -/
theorem affineResidualInclusion_comparison (i : InvariantAffineIndex n)
    (z : affineOrbitOpen n i) :
    affineResidualInclusion n i (orbitToResidualSpectrum n i z) = z.val := by
  rw [← affineResidualRingedIso_base n i z]
  change ((invariantOrbitAffineIso n i).hom ≫ affineResidualInclusion n i) z = z.val
  simp only [affineResidualInclusion, Iso.hom_inv_id_assoc]
  rfl

/-- The original affine parameter projection retains the exact ambient scheme map. -/
@[reassoc] theorem affineResidualProjection_inclusion (i : InvariantAffineIndex n) :
    affineResidualProjection n i ≫ affineResidualInclusion n i =
      (invariantAffineInclusion n i ≫ normalizedDisjointInclusion n i.1) ≫
        invariantOrbitSchemeProjection n := by
  apply Scheme.Hom.ext'
  change (affineResidualProjection n i).toLRSHom ≫
    (affineResidualRingedIso n i).inv ≫
      (invariantLocallyRingedSpace n).ofRestrict (affineOrbitOpen n i).isOpenEmbedding = _
  rw [← affineToInvariantOpen_residualComparison]
  change (affineToInvariantOpen n i ≫ (affineResidualRingedIso n i).hom) ≫ _ = _
  rw [Category.assoc, Iso.hom_inv_id_assoc, affineToInvariantOpen_comp]
  exact (Category.assoc _ _ _).symm

/-- The actual full residual spectra form an open cover of the invariant quotient scheme. -/
def affineResidualSchemeCover : (invariantOrbitScheme n).OpenCover where
  I₀ := InvariantAffineIndex n
  X := affineResidualSpectrum n
  f := affineResidualInclusion n
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    refine ⟨?_, inferInstance⟩
    intro z
    obtain ⟨i, hi⟩ := affineOrbitOpen_covers n z
    exact ⟨i, orbitToResidualSpectrum n i ⟨z, hi⟩,
      affineResidualInclusion_comparison n i ⟨z, hi⟩⟩

/-- The residual affine atlas has the original finite index set. -/
instance affineResidualSchemeCoverFintype : Fintype (affineResidualSchemeCover n).I₀ :=
  inferInstanceAs (Fintype (InvariantAffineIndex n))

/-- Every chart of this cover is the spectrum of its full invariant section ring. -/
instance affineResidualSchemeCover_isAffine (i : (affineResidualSchemeCover n).I₀) :
    IsAffine ((affineResidualSchemeCover n).X i) := by
  change IsAffine (Spec (.of (affineResidualSections n i)))
  infer_instance

/-- The actual full quotient scheme is quasi-compact. -/
instance invariantOrbitScheme_compactSpace : CompactSpace (invariantOrbitScheme n) :=
  (affineResidualSchemeCover n).compactSpace

end FLT.Mazur.CyclicCharacteristicOrbit
