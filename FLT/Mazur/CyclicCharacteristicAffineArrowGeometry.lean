/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicCharacteristicAffineGeometricResidual
public import FLT.Mazur.CyclicCharacteristicAffineOverlapArrows
public import FLT.Mazur.SchemeAffineRelationRestriction

/-!
# Affineness of the entire restricted comparison scheme

The full subgroup-preserving relation is affine over the parameter product.
Its simultaneous restriction to two affine endpoint charts is therefore affine,
including cross-chart and infinitesimal arrows. Saturation identifies the
same-chart restriction with the original full residual domain.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace
namespace FLT.Mazur.CyclicCharacteristicOrbit
open CyclicCharacteristicAtlas
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (n : ℕ) [NeZero n] (i j : InvariantAffineIndex n)

/-- The complete relation between two selected affine charts is an affine open. -/
theorem affineOverlapDomain_isAffineOpen : IsAffineOpen (affineOverlapDomain n i j) := by
  let h := normalizedProduct_isPullback n i.1 j.1
  let a := productSubgroupStructure n i.1 j.1 ≫ h.isoPullback.hom
  have H := SchemeAffineRelationRestriction.isAffineOpen_relation
    (normalizedLocusToInt n i.1) (normalizedLocusToInt n j.1) a
    (isAffineOpen_opensRange (invariantAffineInclusion n i))
    (isAffineOpen_opensRange (invariantAffineInclusion n j))
  dsimp only [a] at H
  rw [Category.assoc, h.isoPullback_hom_fst,
    Category.assoc, h.isoPullback_hom_snd] at H
  exact H

/-- Every full affine-chart overlap retains an affine arrow scheme. -/
instance affineOverlapDomain_isAffine : IsAffine (affineOverlapDomain n i j).toScheme :=
  affineOverlapDomain_isAffineOpen n i j

/-- Saturation identifies the two-endpoint restriction with the original residual domain. -/
theorem affineOverlapDomain_self : affineOverlapDomain n i i = affineResidualDomain n i := by
  change affineResidualDomain n i ⊓ _ = _
  rw [← affineResidualDomain_target, inf_idem]

/-- The original residual domain itself is affine, without discarding nilpotents. -/
instance affineResidualDomain_isAffine : IsAffine (affineResidualDomain n i).toScheme := by
  have h := affineOverlapDomain_isAffineOpen n i i
  rwa [affineOverlapDomain_self] at h

/-- Its actual section ring is Noetherian. -/
instance affineResidualDomain_sections_isNoetherianRing :
    IsNoetherianRing Γ((affineResidualDomain n i).toScheme, ⊤) :=
  IsLocallyNoetherian.component_noetherian
    ⟨⊤, isAffineOpen_top (affineResidualDomain n i).toScheme⟩

end FLT.Mazur.CyclicCharacteristicOrbit
