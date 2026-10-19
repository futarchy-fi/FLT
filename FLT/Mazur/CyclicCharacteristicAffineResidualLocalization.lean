/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicCharacteristicAffineResidualPrincipal
public import FLT.Mazur.CyclicCharacteristicInvariantPrincipalSpectrum

/-!
# Localization of actual quotient sections at full affine residual functions

Transfer the proved invariant localization along the actual residual section
ring equivalence. The ring map remains the original restriction after inverse
reconstruction, so this localization retains all full comparison arrows.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace
namespace FLT.Mazur.CyclicCharacteristicOrbit
open CyclicCharacteristicAtlas
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (n : ℕ) [NeZero n] (i : InvariantAffineIndex n) (s : affineResidualSections n i)

/-- The ambient quotient unit locus of the reconstructed full residual function. -/
def affineResidualAmbientPrincipal : Opens (Orbit n) :=
  invariantPrincipal n (affineOrbitOpen n i) ((affineResidualSectionsEquiv n i).symm s)

/-- This actual principal neighborhood stays within the selected quotient open. -/
theorem affineResidualAmbientPrincipal_le :
    affineResidualAmbientPrincipal n i s ≤ affineOrbitOpen n i :=
  invariantPrincipal_le n _ _

/-- Reconstruct the full residual function and apply the original sheaf restriction. -/
def affineResidualPrincipalRestriction : affineResidualSections n i →+*
    (invariantSheaf n).obj.obj (op (affineResidualAmbientPrincipal n i s)) :=
  (principalRestriction n (affineOrbitOpen n i) ((affineResidualSectionsEquiv n i).symm s)).comp
    (affineResidualSectionsEquiv n i).symm.toRingHom

/-- Restriction agrees with the original invariant sheaf restriction on reconstructed sections. -/
theorem affineResidualPrincipalRestriction_section
    (a : (invariantSheaf n).obj.obj (op (affineOrbitOpen n i))) :
    affineResidualPrincipalRestriction n i s (affineResidualSectionMap n i a) =
      principalRestriction n (affineOrbitOpen n i)
        ((affineResidualSectionsEquiv n i).symm s) a := by
  change principalRestriction n _ _
    ((affineResidualSectionsEquiv n i).symm (affineResidualSectionsEquiv n i a)) = _
  rw [RingEquiv.symm_apply_apply]

/-- The full residual coefficient becomes a unit on its actual quotient neighborhood. -/
theorem affineResidualPrincipalRestriction_isUnit :
    IsUnit (affineResidualPrincipalRestriction n i s s) :=
  principalRestriction_isUnit n _ _

/-- The actual section ring of the reconstructed principal domain is a residual localization. -/
theorem affineResidualPrincipalRestriction_isLocalization :
    @IsLocalization.Away _ _ s
      ((invariantSheaf n).obj.obj (op (affineResidualAmbientPrincipal n i s))) _
      (affineResidualPrincipalRestriction n i s).toAlgebra := by
  let t := (affineResidualSectionsEquiv n i).symm s
  let _ := (principalRestriction n (affineOrbitOpen n i) t).toAlgebra
  let _ := principalRestriction_isLocalization n (affineOrbitOpen n i) t
  have h := IsLocalization.isLocalization_of_base_ringEquiv (.powers t)
    ((invariantSheaf n).obj.obj (op (invariantPrincipal n (affineOrbitOpen n i) t)))
    (affineResidualSectionsEquiv n i)
  rw [Submonoid.map_powers, show affineResidualSectionsEquiv n i t = s from
    (affineResidualSectionsEquiv n i).apply_symm_apply s] at h
  exact h

/-- The localized residual ring is canonically the actual principal-domain section ring. -/
def affineResidualPrincipalSectionEquiv :
    let _ := (affineResidualPrincipalRestriction n i s).toAlgebra
    Localization.Away s ≃ₐ[affineResidualSections n i]
      ((invariantSheaf n).obj.obj (op (affineResidualAmbientPrincipal n i s))) := by
  let _ := (affineResidualPrincipalRestriction n i s).toAlgebra
  let _ := affineResidualPrincipalRestriction_isLocalization n i s
  exact IsLocalization.algEquiv (.powers s) _ _

/-- The localization comparison preserves the exact reconstructed restriction map. -/
theorem affineResidualPrincipalSectionEquiv_algebraMap (a : affineResidualSections n i) :
    affineResidualPrincipalSectionEquiv n i s
      (algebraMap (affineResidualSections n i) (Localization.Away s) a) =
        affineResidualPrincipalRestriction n i s a := by
  let _ := (affineResidualPrincipalRestriction n i s).toAlgebra
  exact (affineResidualPrincipalSectionEquiv n i s).commutes a

end FLT.Mazur.CyclicCharacteristicOrbit
