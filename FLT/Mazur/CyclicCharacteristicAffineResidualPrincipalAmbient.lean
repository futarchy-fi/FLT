/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicCharacteristicAffineResidualLocalization

/-!
# The ambient and restricted full residual principal domains coincide

The restriction stalk isomorphism identifies the unit tests in the original
quotient with those in its selected affine-source orbit open. Consequently the
localization domain is exactly the preimage of the residual spectrum basic open.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace
namespace FLT.Mazur.CyclicCharacteristicOrbit
open CyclicCharacteristicAtlas
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (n : ℕ) [NeZero n] (i : InvariantAffineIndex n) (s : affineResidualSections n i)

/-- The actual restriction stalk identifies the two unit tests of a residual function. -/
theorem affineResidualPrincipal_mem_ambient (z : affineOrbitOpen n i) :
    z ∈ affineResidualPrincipal n i s ↔ z.val ∈ affineResidualAmbientPrincipal n i s := by
  rw [affineResidualPrincipal_eq_basicOpen]
  rw [RingedSpace.mem_top_basicOpen]
  change IsUnit ((invariantOpenSpace n (affineOrbitOpen n i)).presheaf.Γgerm z
    ((invariantOpenSectionsIso n _).inv ((affineResidualSectionsEquiv n i).symm s))) ↔
    z.val ∈ (invariantLocallyRingedSpace n).toRingedSpace.basicOpen
      ((affineResidualSectionsEquiv n i).symm s)
  rw [RingedSpace.mem_basicOpen _ _ _ z.property]
  let e := (invariantLocallyRingedSpace n).restrictStalkIso
    (Opens.isOpenEmbedding (X := space n) (affineOrbitOpen n i)) z
  rw [← isUnit_map_iff e.hom.hom]
  apply (congrArg IsUnit ?_).to_iff
  refine ((invariantLocallyRingedSpace n).restrictStalkIso_hom_eq_germ_apply
    (Opens.isOpenEmbedding (X := space n) (affineOrbitOpen n i)) ⊤ z (by trivial)
    ((invariantOpenSectionsIso n _).inv ((affineResidualSectionsEquiv n i).symm s))).trans ?_
  change TopCat.Presheaf.germ (invariantSheaf n).obj _ z.val _
    ((invariantSheaf n).obj.map _ ((affineResidualSectionsEquiv n i).symm s)) = _
  exact TopCat.Presheaf.germ_res_apply _ _ _ _ _

/-- Pulling the ambient localization domain back to the orbit open gives its residual principal. -/
theorem affineResidualAmbientPrincipal_preimage :
    Subtype.val ⁻¹' (affineResidualAmbientPrincipal n i s : Set (Orbit n)) =
      (affineResidualPrincipal n i s : Set (affineOrbitOpen n i)) := by
  ext z
  exact (affineResidualPrincipal_mem_ambient n i s z).symm

/-- The ambient localization domain is exactly the image of the residual principal domain. -/
theorem affineResidualPrincipal_ambient_image :
    Subtype.val '' (affineResidualPrincipal n i s : Set (affineOrbitOpen n i)) =
      (affineResidualAmbientPrincipal n i s : Set (Orbit n)) := by
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (affineResidualPrincipal_mem_ambient n i s x).mp hx
  · intro hz
    refine ⟨⟨z, affineResidualAmbientPrincipal_le n i s hz⟩, ?_, rfl⟩
    exact (affineResidualPrincipal_mem_ambient n i s _).mpr hz

end FLT.Mazur.CyclicCharacteristicOrbit
