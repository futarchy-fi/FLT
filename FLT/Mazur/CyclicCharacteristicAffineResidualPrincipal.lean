/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicCharacteristicAffineResidualRingedComparison

/-!
# Full affine residual principal domains are actual unit loci

Identify the spectrum-defined principal neighborhoods with the unit loci in
the original locally ringed quotient. The original affine source detects this
identification, so no quotient affineness or point separation is assumed.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
namespace FLT.Mazur.CyclicCharacteristicOrbit
open CyclicCharacteristicAtlas
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (n : ℕ) [NeZero n] (i : InvariantAffineIndex n)

/-- Pullback of the actual unit locus is the basic open of the retained residual function. -/
theorem affineResidualUnitLocus_preimage (s : affineResidualSections n i) :
    (Opens.map (affineToInvariantOpen n i).base).obj
      ((invariantOpenSpace n (affineOrbitOpen n i)).toRingedSpace.basicOpen
        ((invariantOpenSectionsIso n _).inv ((affineResidualSectionsEquiv n i).symm s))) =
      (invariantAffineChart n i).basicOpen s.val := by
  have hv := congrArg Subtype.val ((affineResidualSectionsEquiv n i).apply_symm_apply s)
  change affineInvariantSectionMap n i ((affineResidualSectionsEquiv n i).symm s) = s.val at hv
  have he := LocallyRingedSpace.preimage_basicOpen (affineToInvariantOpen n i)
    ((invariantOpenSectionsIso n _).inv ((affineResidualSectionsEquiv n i).symm s))
  change _ = (invariantAffineChart n i).basicOpen
    (affineInvariantSectionMap n i ((affineResidualSectionsEquiv n i).symm s)) at he
  rwa [hv] at he

/-- Spectrum principal neighborhoods are exactly the original quotient's unit loci. -/
theorem affineResidualPrincipal_eq_basicOpen (s : affineResidualSections n i) :
    affineResidualPrincipal n i s =
      (invariantOpenSpace n (affineOrbitOpen n i)).toRingedSpace.basicOpen
        ((invariantOpenSectionsIso n _).inv ((affineResidualSectionsEquiv n i).symm s)) := by
  apply Opens.ext
  apply (Set.preimage_injective.mpr (affineOrbitProjection_surjective n i))
  have he := congrArg SetLike.coe (affineResidualUnitLocus_preimage n i s)
  rw [affineToInvariantOpen_base] at he
  exact (affineResidualPrincipal_preimage n i s).trans he.symm

/-- The full residual principal domain is exactly the image of the original affine basic open. -/
theorem affineResidualPrincipal_image (s : affineResidualSections n i) :
    affineOrbitProjection n i ''
      ((invariantAffineChart n i).basicOpen s.val : Set (invariantAffineChart n i)) =
      (affineResidualPrincipal n i s).carrier := by
  have h := congrArg (fun S : Set (invariantAffineChart n i) =>
    affineOrbitProjection n i '' S) (affineResidualPrincipal_preimage n i s)
  exact h.symm.trans (Set.image_preimage_eq _ (affineOrbitProjection_surjective n i))

/-- Multiplication intersects the actual full residual principal neighborhoods. -/
theorem affineResidualPrincipal_mul (s t : affineResidualSections n i) :
    affineResidualPrincipal n i (s * t) =
      affineResidualPrincipal n i s ⊓ affineResidualPrincipal n i t := by
  simp only [affineResidualPrincipal_eq_basicOpen, map_mul]
  exact RingedSpace.basicOpen_mul _ _ _

/-- The unit function gives the whole selected quotient open. -/
theorem affineResidualPrincipal_one : affineResidualPrincipal n i 1 = ⊤ := by
  rw [affineResidualPrincipal_eq_basicOpen, map_one, map_one]
  exact RingedSpace.basicOpen_of_isUnit _ isUnit_one

/-- Positive powers preserve the actual full residual principal neighborhood. -/
theorem affineResidualPrincipal_pow (s : affineResidualSections n i) (k : ℕ) (hk : 0 < k) :
    affineResidualPrincipal n i (s ^ k) = affineResidualPrincipal n i s := by
  simp only [affineResidualPrincipal_eq_basicOpen, map_pow]
  exact RingedSpace.basicOpen_pow _ _ k hk

end FLT.Mazur.CyclicCharacteristicOrbit
