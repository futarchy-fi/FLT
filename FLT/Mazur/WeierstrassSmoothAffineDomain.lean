/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSmoothChartCompatibility

/-!
# The full smooth affine input domain

Every pair of relatively smooth affine inputs lies in the domain of the
original partial addition. Its inverse image in an addition chart is exactly
the previously constructed smooth-input open.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

/-- The open where both projections of the affine product are relatively smooth. -/
def smoothAffineInputOpen : (Spec (.of (AffineProduct W))).Opens :=
  Spec.map (CommRingCat.ofHom (productLeft W).toRingHom) ⁻¹ᵁ
      (chartStructure W 2).smoothLocus ⊓
    Spec.map (CommRingCat.ofHom (productRight W).toRingHom) ⁻¹ᵁ
      (chartStructure W 2).smoothLocus

/-- Every smooth affine input pair belongs to the original four-chart addition domain. -/
theorem smoothAffineInputOpen_le_domain : smoothAffineInputOpen W ≤ affineAdditionDomain W := by
  intro p hp
  apply mem_affineAdditionDomain_of_nonsingular
  exact affineAlgebra_residue_nonsingular_at W (productLeft W) p hp.1

/-- The left chart input is the left projection after the original chart inclusion. -/
theorem additionChartInclusion_left (i : AdditionChartIndex) :
    additionChartInclusion W i ≫ Spec.map (CommRingCat.ofHom (productLeft W).toRingHom) =
      Spec.map (CommRingCat.ofHom (additionInputLeft W i).toRingHom) := by
  rw [additionChartInclusion.eq_def, ← additionChartAlgRestriction_toRingHom,
    ← Spec.map_comp]
  rfl

/-- The right chart input is the right projection after the original chart inclusion. -/
theorem additionChartInclusion_right (i : AdditionChartIndex) :
    additionChartInclusion W i ≫ Spec.map (CommRingCat.ofHom (productRight W).toRingHom) =
      Spec.map (CommRingCat.ofHom (additionInputRight W i).toRingHom) := by
  rw [additionChartInclusion.eq_def, ← additionChartAlgRestriction_toRingHom,
    ← Spec.map_comp]
  rfl

/-- Restricting the affine input product recovers the actual chart smooth-input open. -/
theorem additionSmoothInputOpen_preimage (i : AdditionChartIndex) :
    additionChartInclusion W i ⁻¹ᵁ smoothAffineInputOpen W = additionSmoothInputOpen W i := by
  ext p
  change (_ ∈ (chartStructure W 2).smoothLocus ∧
    _ ∈ (chartStructure W 2).smoothLocus) ↔ _
  have hl := congrArg (fun f => f p) (additionChartInclusion_left W i)
  have hr := congrArg (fun f => f p) (additionChartInclusion_right W i)
  change (Spec.map _ ((additionChartInclusion W i) p) ∈ _ ∧
    Spec.map _ ((additionChartInclusion W i) p) ∈ _) ↔ _
  simp only [Scheme.Hom.comp_apply] at hl hr
  rw [hl, hr]
  rfl

/-- The entire smooth affine input open maps to the original partial addition domain. -/
def smoothAffineInputToDomain :
    (smoothAffineInputOpen W).toScheme ⟶ (affineAdditionDomain W).toScheme :=
  IsOpenImmersion.lift (affineAdditionDomain W).ι (smoothAffineInputOpen W).ι (by
    rw [Scheme.Opens.range_ι, Scheme.Opens.range_ι]
    exact smoothAffineInputOpen_le_domain W)

/-- The domain factorization preserves the original affine product inclusion. -/
@[reassoc] theorem smoothAffineInputToDomain_inclusion :
    smoothAffineInputToDomain W ≫ (affineAdditionDomain W).ι = (smoothAffineInputOpen W).ι :=
  IsOpenImmersion.lift_fac _ _ _

/-- The smooth affine input locus is an open subscheme of the partial addition domain. -/
instance smoothAffineInputToDomain_isOpenImmersion :
    IsOpenImmersion (smoothAffineInputToDomain W) :=
  inferInstanceAs (IsOpenImmersion (IsOpenImmersion.lift _ _ _))

end FLT.Mazur.WeierstrassIntegralChart
