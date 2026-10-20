/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicCharacteristicAffineResidualIsomorphism

/-!
# Scheme structure on the original invariant orbit space

The proved residual charts supply the local-affineness field of the original
locally ringed orbit space. Its carrier, invariant sheaf, and source projection
are retained without replacement.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Opposite
namespace FLT.Mazur.CyclicCharacteristicOrbit
open CyclicCharacteristicAtlas
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (n : ℕ) [NeZero n]

/-- The actual orbit space with its invariant sheaf is a scheme. -/
def invariantOrbitScheme : Scheme where
  toLocallyRingedSpace := invariantLocallyRingedSpace n
  local_affine z := by
    obtain ⟨i, hi⟩ := affineOrbitOpen_covers n z
    exact ⟨⟨affineOrbitOpen n i, hi⟩, CommRingCat.of (affineResidualSections n i),
      ⟨affineResidualRingedIso n i⟩⟩

/-- The original locally ringed source projection is now a scheme morphism. -/
def invariantOrbitSchemeProjection : normalizedDisjointSource n ⟶ invariantOrbitScheme n :=
  ⟨invariantLocallyRingedProjection n⟩

/-- Its underlying map is exactly the original orbit projection. -/
theorem invariantOrbitSchemeProjection_apply (x : normalizedDisjointSource n) :
    invariantOrbitSchemeProjection n x = projection n x :=
  congrArg (fun f => f x) (invariantLocallyRingedProjection_base n)

/-- Every point of the quotient scheme comes from the original assembled source. -/
theorem invariantOrbitSchemeProjection_surjective :
    Function.Surjective (invariantOrbitSchemeProjection n) := by
  intro z
  obtain ⟨x, hx⟩ := projection_surjective n z
  exact ⟨x, (invariantOrbitSchemeProjection_apply n x).trans hx⟩

/-- Equality under the scheme projection is exactly the original full point relation. -/
theorem invariantOrbitSchemeProjection_eq_iff (x y : normalizedDisjointSource n) :
    invariantOrbitSchemeProjection n x = invariantOrbitSchemeProjection n y ↔ Related n x y := by
  rw [invariantOrbitSchemeProjection_apply, invariantOrbitSchemeProjection_apply,
    projection_eq_iff]

/-- The original full residual comparison gives an affine chart on this same scheme. -/
def invariantOrbitAffineIso (i : InvariantAffineIndex n) :
    (show (invariantOrbitScheme n).Opens from affineOrbitOpen n i).toScheme ≅
      affineResidualSpectrum n i :=
  { hom := ⟨(affineResidualRingedIso n i).hom⟩
    inv := ⟨(affineResidualRingedIso n i).inv⟩
    hom_inv_id := by
      apply Scheme.Hom.ext'
      exact (affineResidualRingedIso n i).hom_inv_id
    inv_hom_id := by
      apply Scheme.Hom.ext'
      exact (affineResidualRingedIso n i).inv_hom_id }

end FLT.Mazur.CyclicCharacteristicOrbit
