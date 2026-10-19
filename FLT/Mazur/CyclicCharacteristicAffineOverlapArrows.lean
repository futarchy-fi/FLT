/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicCharacteristicAffineOrbitLocallyRinged

/-!
# Full comparison arrows between the actual affine refinements

For any two selected affine charts, retain the open of the entire original
comparison scheme where both endpoints lie in those charts. This includes the
cross-characteristic arrows; no finite relabeling relation replaces them.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.CyclicCharacteristicOrbit
open CyclicCharacteristicAtlas
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (n : ℕ) [NeZero n] (i j : InvariantAffineIndex n)

/-- All original comparison arrows whose endpoints lie in the two selected affine charts. -/
def affineOverlapDomain : (productSubgroupScheme n i.1 j.1).Opens :=
  productArrowSource n i.1 j.1 ⁻¹ᵁ (invariantAffineInclusion n i).opensRange ⊓
    productArrowTarget n i.1 j.1 ⁻¹ᵁ (invariantAffineInclusion n j).opensRange

/-- The source endpoint in its actual original affine chart. -/
def affineOverlapSource : (affineOverlapDomain n i j).toScheme ⟶ invariantAffineChart n i :=
  IsOpenImmersion.lift (invariantAffineInclusion n i)
    ((affineOverlapDomain n i j).ι ≫ productArrowSource n i.1 j.1) (by
      rintro _ ⟨x, rfl⟩
      exact x.property.1)

/-- The target endpoint in its original affine chart, possibly in the other characteristic. -/
def affineOverlapTarget : (affineOverlapDomain n i j).toScheme ⟶ invariantAffineChart n j :=
  IsOpenImmersion.lift (invariantAffineInclusion n j)
    ((affineOverlapDomain n i j).ι ≫ productArrowTarget n i.1 j.1) (by
      rintro _ ⟨x, rfl⟩
      exact x.property.2)

/-- The refined source retains the original full comparison morphism. -/
@[reassoc] theorem affineOverlapSource_inclusion :
    affineOverlapSource n i j ≫ invariantAffineInclusion n i =
      (affineOverlapDomain n i j).ι ≫ productArrowSource n i.1 j.1 :=
  IsOpenImmersion.lift_fac _ _ _

/-- The refined target retains the original full comparison morphism. -/
@[reassoc] theorem affineOverlapTarget_inclusion :
    affineOverlapTarget n i j ≫ invariantAffineInclusion n j =
      (affineOverlapDomain n i j).ι ≫ productArrowTarget n i.1 j.1 :=
  IsOpenImmersion.lift_fac _ _ _

/-- Both refined endpoints agree as locally ringed maps to the full invariant quotient. -/
theorem affineOverlap_projection_condition :
    (affineOverlapSource n i j).toLRSHom ≫ affineLocallyRingedProjection n i =
      (affineOverlapTarget n i j).toLRSHom ≫ affineLocallyRingedProjection n j := by
  simp only [affineLocallyRingedProjection, ← Category.assoc,
    ← Scheme.Hom.comp_toLRSHom, affineOverlapSource_inclusion, affineOverlapTarget_inclusion]
  simp only [Scheme.Hom.comp_toLRSHom, Category.assoc,
    chartLocallyRingedProjection_condition]

end FLT.Mazur.CyclicCharacteristicOrbit
