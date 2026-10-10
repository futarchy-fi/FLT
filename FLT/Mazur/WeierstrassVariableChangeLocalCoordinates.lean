/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.WeierstrassVariableChangeCoordinateCover

/-!
# Coordinates on the principal refinements of the cubic

The transformed tuple satisfies the original equation after localization.
Its selected coordinate is a concrete unit, so it gives an actual chart point.
-/

@[expose] public noncomputable section

open WeierstrassCurve AlgebraicGeometry CategoryTheory

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace FLT.Mazur.WeierstrassVariableChangeHomogeneous

variable {R S : Type*} [CommRing R] [CommRing S]

/-- Homogeneous coordinate transport commutes with any ring map. -/
theorem coordinates_map (C : VariableChange R) (P : Fin 3 → R) (f : R →+* S) :
    coordinates (C.map f) (f ∘ P) = f ∘ coordinates C P := by
  ext i
  fin_cases i <;> simp [coordinates, VariableChange.map]

end FLT.Mazur.WeierstrassVariableChangeHomogeneous

namespace FLT.Mazur.WeierstrassIntegralChart

variable {R : Type} [CommRing R] (W : WeierstrassCurve R) (C : VariableChange R)

/-- The universal transformed tuple already satisfies the original cubic. -/
theorem changedCoordinates_equation (j : Fin 3) :
    (W.map (algebraMap R (Coordinate (C • W) j))).toProjective.Equation
      (changedCoordinates W C j) := by
  apply (WeierstrassVariableChangeHomogeneous.equation_iff _ _ _).mpr
  rw [map_variableChange]
  exact coord_equation (C • W) j

/-- The actual coefficient ring of a principal refinement. -/
abbrev ChangedLocalization (j k : Fin 3) :=
  Localization.Away (changedCoordinates W C j k)

/-- The original normalized tuple on the localization. -/
def localizedInput (j k : Fin 3) : Fin 3 → ChangedLocalization W C j k :=
  algebraMap (Coordinate (C • W) j) _ ∘ coord (C • W) j

/-- The transformed tuple on the localization, before normalizing its output. -/
def localizedOutput (j k : Fin 3) : Fin 3 → ChangedLocalization W C j k :=
  algebraMap (Coordinate (C • W) j) _ ∘ changedCoordinates W C j

/-- Localizing the transformed tuple agrees with transforming the localized input. -/
theorem localizedOutput_eq (j k : Fin 3) :
    localizedOutput W C j k = WeierstrassVariableChangeHomogeneous.coordinates
      (C.map (algebraMap R (ChangedLocalization W C j k))) (localizedInput W C j k) := by
  simp only [localizedInput, localizedOutput, changedCoordinates]
  rw [← WeierstrassVariableChangeHomogeneous.coordinates_map, VariableChange.map_map,
    ← IsScalarTower.algebraMap_eq]

/-- The localized output satisfies the original equation as a polynomial identity. -/
theorem localizedOutput_equation (j k : Fin 3) :
    (W.map (algebraMap R (ChangedLocalization W C j k))).toProjective.Equation
      (localizedOutput W C j k) := by
  have h := (changedCoordinates_equation W C j).map
    (algebraMap (Coordinate (C • W) j) (ChangedLocalization W C j k))
  simpa only [WeierstrassCurve.map_map, ← IsScalarTower.algebraMap_eq,
    localizedOutput] using h

/-- The selected output coordinate is invertible in the actual localization. -/
def localizedOutputUnit (j k : Fin 3) : (ChangedLocalization W C j k)ˣ :=
  (IsLocalization.Away.algebraMap_isUnit (changedCoordinates W C j k)
    (S := ChangedLocalization W C j k)).unit

/-- The chosen unit has exactly the selected transformed coordinate as its value. -/
theorem localizedOutputUnit_val (j k : Fin 3) :
    (localizedOutputUnit W C j k : ChangedLocalization W C j k) =
      localizedOutput W C j k k := IsUnit.unit_spec _

/-- The normalized input remains normalized after localization. -/
theorem localizedInput_self (j k : Fin 3) : localizedInput W C j k j = 1 := by
  simp [localizedInput, coord_self]

end FLT.Mazur.WeierstrassIntegralChart
