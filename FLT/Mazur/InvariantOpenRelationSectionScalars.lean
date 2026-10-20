/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RelativeRelationMinimalScalarEndpoints
public import FLT.Mazur.SchemeRelationSectionScalars

/-!
# Original orbit-open scalars in the full scheme equalizer

The invariant sheaf on the prescribed orbit open is the compatible-function
ring for its entire restricted relation. The identification preserves the
literal scalar action on every original section ring and both endpoints.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Opposite
namespace FLT.Mazur.InvariantOpenRelationDiagram
open RelativeRelationOrbit SchemeEffectiveEpiSections SchemeRelationSectionScalars
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {S : Scheme.{0}} {D A : Over S} {p q : D ⟶ A}
  (e : CategoryTheory.EquivalenceRelation p q)
  (W : TopologicalSpace.Opens (Orbit e))
set_option quotPrecheck false
local notation "E" => (pullOpen e W).val
local notation "Ω" => (invariantSheaf e).obj.obj (op W)
local notation "p₀" => (fst p E).left
local notation "q₀" => (snd p q E (pullOpen_preimage_eq e W)).left

/-- The original scalar ring is the equalizer of the entire restricted scheme relation. -/
def orbitCompatibleFunctions : Ω ≃+* compatibleFunctions p₀ q₀ :=
  orbitFunctions e W

/-- The equalizer comparison preserves the original source scalar inclusion. -/
theorem orbitCompatibleFunctions_val (t : Ω) :
    (orbitCompatibleFunctions e W t).val = orbitScalarCoordinates e W t := rfl

/-- Every open section action transports to the literal original scalar pullback. -/
theorem orbitCompatibleFunctions_scalarMap {Y : Scheme.{0}}
    (g : Y ⟶ (E).toScheme) (U : Y.Opens) :
    (scalarMap p₀ q₀ g U).comp (orbitCompatibleFunctions e W).toRingHom =
      (g.appLE ⊤ U le_top).hom.comp (orbitScalarCoordinates e W) := rfl

/-- Both original endpoints give exactly the same action of the orbit-open scalars. -/
theorem orbitScalarCoordinates_relation {Y : Scheme.{0}}
    (δ : Y ⟶ (relation p E).left) (U : Y.Opens) :
    ((δ ≫ p₀).appLE ⊤ U le_top).hom.comp (orbitScalarCoordinates e W) =
      ((δ ≫ q₀).appLE ⊤ U le_top).hom.comp (orbitScalarCoordinates e W) := by
  rw [← orbitCompatibleFunctions_scalarMap, ← orbitCompatibleFunctions_scalarMap,
    scalarMap_relation]

end FLT.Mazur.InvariantOpenRelationDiagram
