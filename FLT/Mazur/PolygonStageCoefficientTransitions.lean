/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonParameterProjectionComposition
public import FLT.Mazur.PolygonStageCoefficientFamilies

/-!
# Coefficient change commutes with the original stage transitions

The concrete ring square gives equality of the actual glued family maps.
These equalities will assemble the marked coefficient comparison of systems.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.PolygonInfinitesimalStages
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R S T : Type} [CommRing R] [CommRing S] [CommRing T]

/-- The original finite-base coefficient square commutes with adjacent restriction. -/
@[reassoc] theorem stageCoefficientBase_restriction (f : R →+* S) (m : ℕ) :
    baseRestriction S m ≫ stageCoefficientBase f (m + 1) =
      stageCoefficientBase f m ≫ baseRestriction R m := by
  simp only [baseRestriction, stageCoefficientBase, ← Spec.map_comp,
    ← CommRingCat.ofHom_comp, stageCoefficientMap_restriction]

/-- The original whole-family coefficient square commutes with adjacent restriction. -/
@[reassoc] theorem stageCoefficientFamily_restriction (f : R →+* S)
    (m n : ℕ) (h : 2 ≤ n) :
    stageRestriction S m n h ≫ stageCoefficientFamily f (m + 1) n h =
      stageCoefficientFamily f m n h ≫ stageRestriction R m n h := by
  simp only [stageRestriction, stageCoefficientFamily,
    PolygonInfinitesimal.parameterProjection_comp]
  congr 1
  exact stageCoefficientMap_restriction f m

/-- Identity coefficient change fixes every original finite family. -/
theorem stageCoefficientFamily_id (m n : ℕ) (h : 2 ≤ n) :
    stageCoefficientFamily (RingHom.id R) m n h = 𝟙 _ := by
  change PolygonInfinitesimal.parameterProjection _ (parameter R m) (parameter R m)
    (stageCoefficientMap_parameter (RingHom.id R) m) n h =
      𝟙 (PolygonInfinitesimal.scheme (Ring R m) (parameter R m) n h)
  simp only [stageCoefficientMap_id, PolygonInfinitesimal.parameterProjection_id]

/-- Coefficient changes compose on the actual finite families. -/
@[reassoc] theorem stageCoefficientFamily_comp (f : R →+* S) (g : S →+* T)
    (m n : ℕ) (h : 2 ≤ n) :
    stageCoefficientFamily g m n h ≫ stageCoefficientFamily f m n h =
      stageCoefficientFamily (g.comp f) m n h := by
  simp only [stageCoefficientFamily, PolygonInfinitesimal.parameterProjection_comp,
    stageCoefficientMap_comp]

end FLT.Mazur.PolygonInfinitesimalStages
