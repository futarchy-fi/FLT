/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.BaseAdicReesModelSectionCoordinates

/-!
# Naturality of the original power coordinates

The native coefficient comparison intertwines the original affine restriction
maps. Its source-ring linearity uses the existing action on the original
power sections, without transporting a new action onto those sections.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry
open Scheme.Modules FLT.Mazur.BaseAdicThickening
open scoped TensorProduct

universe u

namespace FLT.Mazur.BaseAdicRees

variable {R : CommRingCat.{u}} {X : Scheme.{u}} (f : X ⟶ Spec R)
  (J : Ideal R) [IsLocallyNoetherian X] (M : X.Modules) [M.IsFinitePresentation]

/-- The inverse coordinates commute with every original affine restriction. -/
lemma nativePowerSectionsEquiv_restriction {U V : X.affineOpens} (h : U.1 ≤ V.1)
    (s : nativeModule f J M V) :
    nativePowerSectionsEquiv f J M U (nativeRestriction f J M h s) =
      IdealPowerRees.chartRestriction ((baseIdeal R J).comap f) M V h le_rfl
        (homOfLE h) (nativePowerSectionsEquiv f J M V s) := by
  let _ := chartAlgebra f U
  let _ := chartAlgebra f V
  apply (sectionsEquiv f J U M).injective
  rw [nativePowerSectionsEquiv_coordinates, sectionsEquiv_restriction,
    nativePowerSectionsEquiv_coordinates]
  rfl

/-- Each recovered homogeneous section restricts by its original power-sheaf map. -/
lemma nativePowerSectionsEquiv_restriction_apply {U V : X.affineOpens}
    (h : U.1 ≤ V.1) (s : nativeModule f J M V) (n : ℕ) :
    nativePowerSectionsEquiv f J M U (nativeRestriction f J M h s) n =
      (GlobalIdealPower.multiple (((baseIdeal R J).comap f) ^ n) M).presheaf.map
        (homOfLE h).op (nativePowerSectionsEquiv f J M V s n) := by
  rw [nativePowerSectionsEquiv_restriction]
  rfl

/-- Native coordinates retain the original action of the source chart ring. -/
lemma nativePowerSectionsEquiv_smul (V : X.affineOpens)
    (a : Γ(X, V.1)) (s : nativeModule f J M V) :
    let _ := chartAlgebra f V
    nativePowerSectionsEquiv f J M V
      (a • (show Rees.extendedModule (S := Γ(X, V.1)) (M := Γ(M, V.1)) J from s)) =
      a • nativePowerSectionsEquiv f J M V s := by
  let _ := chartAlgebra f V
  unfold nativePowerSectionsEquiv
  exact (sectionsEquiv f J V M).symm.map_smul a s

end FLT.Mazur.BaseAdicRees
