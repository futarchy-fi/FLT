/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicCharacteristicAffineOrbitLocallyRinged

/-!
# Full residual arrows on the selected affine parameter charts

Restrict the entire original same-chart comparison scheme to a saturated affine
source domain. Both endpoints factor into that affine chart, with all residual
and infinitesimal arrows still present, and their locally ringed projections agree.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.CyclicCharacteristicOrbit
open CyclicCharacteristicAtlas
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (n : ℕ) [NeZero n] (i : InvariantAffineIndex n)

/-- The full same-chart comparison domain above the selected invariant affine open. -/
def affineResidualDomain : (productSubgroupScheme n i.1 i.1).Opens :=
  productArrowSource n i.1 i.1 ⁻¹ᵁ (invariantAffineInclusion n i).opensRange

/-- Saturation gives exactly the same domain when tested at the other endpoint. -/
theorem affineResidualDomain_target :
    affineResidualDomain n i =
      productArrowTarget n i.1 i.1 ⁻¹ᵁ (invariantAffineInclusion n i).opensRange :=
  invariantAffineInclusion_open_saturated n i

/-- The original source endpoint restricted to the actual affine chart. -/
def affineResidualSource : (affineResidualDomain n i).toScheme ⟶ invariantAffineChart n i :=
  IsOpenImmersion.lift (invariantAffineInclusion n i)
    ((affineResidualDomain n i).ι ≫ productArrowSource n i.1 i.1) (by
      rintro _ ⟨x, rfl⟩
      exact x.property)

/-- The original target endpoint on the same full residual arrow domain. -/
def affineResidualTarget : (affineResidualDomain n i).toScheme ⟶ invariantAffineChart n i :=
  IsOpenImmersion.lift (invariantAffineInclusion n i)
    ((affineResidualDomain n i).ι ≫ productArrowTarget n i.1 i.1) (by
      rintro _ ⟨x, rfl⟩
      exact (Set.ext_iff.mp (congrArg SetLike.coe
        (affineResidualDomain_target n i)) x.val).mp x.property)

/-- Source restriction preserves the original scheme morphism. -/
@[reassoc] theorem affineResidualSource_inclusion :
    affineResidualSource n i ≫ invariantAffineInclusion n i =
      (affineResidualDomain n i).ι ≫ productArrowSource n i.1 i.1 :=
  IsOpenImmersion.lift_fac _ _ _

/-- Target restriction preserves the original scheme morphism. -/
@[reassoc] theorem affineResidualTarget_inclusion :
    affineResidualTarget n i ≫ invariantAffineInclusion n i =
      (affineResidualDomain n i).ι ≫ productArrowTarget n i.1 i.1 :=
  IsOpenImmersion.lift_fac _ _ _

/-- The refined original affine projection retains every full residual comparison. -/
theorem affineToInvariantOpen_condition :
    (affineResidualSource n i).toLRSHom ≫ affineToInvariantOpen n i =
      (affineResidualTarget n i).toLRSHom ≫ affineToInvariantOpen n i := by
  have h : (affineResidualSource n i).toLRSHom ≫ affineLocallyRingedProjection n i =
      (affineResidualTarget n i).toLRSHom ≫ affineLocallyRingedProjection n i := by
    simp only [affineLocallyRingedProjection, ← Category.assoc,
      ← Scheme.Hom.comp_toLRSHom, affineResidualSource_inclusion,
      affineResidualTarget_inclusion]
    simp only [Scheme.Hom.comp_toLRSHom, Category.assoc,
      chartLocallyRingedProjection_condition]
  have hs := congrArg ((affineResidualSource n i).toLRSHom ≫ ·)
    (affineToInvariantOpen_comp n i)
  have ht := congrArg ((affineResidualTarget n i).toLRSHom ≫ ·)
    (affineToInvariantOpen_comp n i)
  let j : invariantOpenSpace n (affineOrbitOpen n i) ⟶ invariantLocallyRingedSpace n :=
    (invariantLocallyRingedSpace n).ofRestrict
      (TopologicalSpace.Opens.isOpenEmbedding (X := space n) (affineOrbitOpen n i))
  have hs' := (Category.assoc (affineResidualSource n i).toLRSHom
    (affineToInvariantOpen n i) j).trans hs
  have ht' := (Category.assoc (affineResidualTarget n i).toLRSHom
    (affineToInvariantOpen n i) j).trans ht
  exact (cancel_mono j).mp (hs'.trans (h.trans ht'.symm))

end FLT.Mazur.CyclicCharacteristicOrbit
