/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonBoundaryCoefficientNaturality
public import FLT.Mazur.PolygonCompatibleHomogeneousSections

/-!
# Coefficient maps of compatible original boundary sections

The compatible ring map is constructed from the actual stage pullbacks.
It retains every evaluation and every homogeneous tensor degree.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.PolygonInfinitesimalStages
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (n : ℕ) (h : 2 ≤ n)

/-- Coefficient pullback assembled in the original compatible-section ring. -/
def compatibleCoefficientRingMap : compatibleSectionRing R n h →+* compatibleSectionRing S n h :=
  compatibleSectionLift S n h
    (fun m ↦ (coefficientBoundarySections f m n h).comp (compatibleSectionEval R n h m))
    (by
      intro a b g
      rw [← RingHom.comp_assoc, coefficientBoundarySections_naturality,
        RingHom.comp_assoc, compatibleSectionEval_transition])

attribute [local semireducible] CompatibleSections

/-- The same constructed coefficient map on the named compatible-section carriers. -/
def compatibleCoefficientMap : CompatibleSections R n h →+* CompatibleSections S n h :=
  compatibleCoefficientRingMap f n h

/-- Each actual stage evaluation is the original boundary section pullback. -/
theorem compatibleCoefficientMap_eval (m : ℕ) (s : CompatibleSections R n h) :
    compatibleEval S n h m (compatibleCoefficientMap f n h s) =
      coefficientBoundarySections f m n h (compatibleEval R n h m s) := rfl

/-- Coefficient pullback preserves the specified tensor degree across all stages. -/
theorem compatibleCoefficientMap_degree (d : ℕ) {s : CompatibleSections R n h}
    (hs : IsCompatibleDegree R n h d s) :
    IsCompatibleDegree S n h d (compatibleCoefficientMap f n h s) := by
  intro m
  rw [compatibleCoefficientMap_eval]
  exact coefficientBoundarySections_mem_grade f m n h (hs m)

end FLT.Mazur.PolygonInfinitesimalStages
