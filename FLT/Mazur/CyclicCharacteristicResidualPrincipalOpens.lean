/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicCharacteristicResidualSectionEquivalence

/-!
# Saturated principal opens from full residual invariants

Every residual invariant gives an actual open of the characteristic quotient.
Its normalized-chart preimage is the ordinary basic open of the residual
function, saturated under the full same-chart comparison. These are concrete
candidate refinements; affineness and coverage by suitable affine candidates
still require the normalized parameter geometry.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace
namespace FLT.Mazur.CyclicCharacteristicOrbit
open CyclicCharacteristicAtlas
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (n : ℕ) [NeZero n] (b : Bool)

/-- The actual quotient-open unit locus of a full normalized-chart residual function. -/
def residualPrincipal (s : chartResidualSections n b) :
    Opens (invariantOpenSpace n (integerOpen n (chartInteger b))) :=
  (invariantOpenSpace n (integerOpen n (chartInteger b))).toRingedSpace.basicOpen
    ((invariantOpenSectionsIso n _).inv ((chartResidualSectionsEquiv n b).symm s))

/-- The residual principal open has exactly the original normalized basic-open preimage. -/
theorem residualPrincipal_chart_preimage (s : chartResidualSections n b) :
    (Opens.map (chartToInvariantOpen n b).base).obj (residualPrincipal n b s) =
      (normalizedLocus n b).basicOpen s.val := by
  have hv := congrArg Subtype.val ((chartResidualSectionsEquiv n b).apply_symm_apply s)
  change chartInvariantSectionMap n b ((chartResidualSectionsEquiv n b).symm s) = s.val at hv
  have he := LocallyRingedSpace.preimage_basicOpen (chartToInvariantOpen n b)
    ((invariantOpenSectionsIso n _).inv ((chartResidualSectionsEquiv n b).symm s))
  change (Opens.map (chartToInvariantOpen n b).base).obj (residualPrincipal n b s) =
    (normalizedLocus n b).basicOpen
      (chartInvariantSectionMap n b ((chartResidualSectionsEquiv n b).symm s)) at he
  rw [hv] at he
  exact he

/-- Every same-chart arrow, including residual arrows, preserves this original basic open. -/
theorem residualBasicOpen_saturated (s : chartResidualSections n b) :
    productArrowSource n b b ⁻¹ᵁ (normalizedLocus n b).basicOpen s.val =
      productArrowTarget n b b ⁻¹ᵁ (normalizedLocus n b).basicOpen s.val := by
  rw [Scheme.preimage_basicOpen_top, Scheme.preimage_basicOpen_top, s.property]

/-- The actual quotient open is exactly the image of its saturated normalized basic open. -/
theorem residualPrincipal_chart_image (s : chartResidualSections n b) :
    (chartToInvariantOpen n b).base '' ((normalizedLocus n b).basicOpen s.val : Set _) =
      (residualPrincipal n b s).carrier := by
  rw [← residualPrincipal_chart_preimage, Opens.map_coe]
  exact Set.image_preimage_eq (residualPrincipal n b s).carrier
    (chartToInvariantOpen_isQuotientMap n b).surjective

/-- Multiplication gives the actual intersection of residual principal neighborhoods. -/
theorem residualPrincipal_mul (s t : chartResidualSections n b) :
    residualPrincipal n b (s * t) = residualPrincipal n b s ⊓ residualPrincipal n b t := by
  unfold residualPrincipal
  rw [map_mul, map_mul, RingedSpace.basicOpen_mul]

/-- The unit residual function recovers the whole characteristic quotient open. -/
theorem residualPrincipal_one : residualPrincipal n b 1 = ⊤ := by
  unfold residualPrincipal
  rw [map_one, map_one]
  exact RingedSpace.basicOpen_of_isUnit _ isUnit_one

end FLT.Mazur.CyclicCharacteristicOrbit
