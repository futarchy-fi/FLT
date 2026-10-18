/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.WeierstrassComparisonCoefficientHom

/-!
# Coherence of coefficient morphisms of full comparison algebras

Identity and composite coefficient maps preserve every universal change
coordinate. Named equations retain all their equality transports.
-/

@[expose] public noncomputable section
open WeierstrassCurve
namespace FLT.Mazur.WeierstrassChangeParameter
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] comparisonPresentationHom
variable {R A B : Type} [CommRing R] [CommRing A] [CommRing B]
  (W V : WeierstrassCurve R) (W' V' : WeierstrassCurve A) (W'' V'' : WeierstrassCurve B)
  (f : R →+* A) (g : A →+* B) (j : R →+* B) (hj : j = g.comp f)
  (hfW : W' = W.map f) (hfV : V' = V.map f)
  (hgW : W'' = W'.map g) (hgV : V'' = V'.map g)
  (hjW : W'' = W.map j) (hjV : V'' = V.map j)

include hj in
/-- Direct and iterated coefficient morphisms agree on the full comparison algebra. -/
theorem comparisonPresentationHom_comp :
    (comparisonPresentationHom W' V' W'' V'' g hgW hgV).comp
      (comparisonPresentationHom W V W' V' f hfW hfV) =
    comparisonPresentationHom W V W'' V'' j hjW hjV := by
  apply comparisonPresentationHom_ext W V W'' V'' j
  · rw [RingHom.comp_assoc, comparisonPresentationHom_base, ← RingHom.comp_assoc,
      comparisonPresentationHom_base, RingHom.comp_assoc, ← hj]
  · exact comparisonPresentationHom_base W V W'' V'' j hjW hjV
  · rw [← VariableChange.map_map, comparisonPresentationHom_change,
      comparisonPresentationHom_change, comparisonPresentationHom_change]

/-- Identity coefficient refinement acts identically on the actual comparison algebra. -/
theorem comparisonPresentationHom_id :
    comparisonPresentationHom W V W V (RingHom.id R)
      (W.map_id.symm) (V.map_id.symm) = RingHom.id (EquationRing W V) := by
  apply comparisonPresentationHom_ext W V W V (RingHom.id R)
  · exact comparisonPresentationHom_base W V W V _ _ _
  · simp only [RingHom.id_comp, RingHom.comp_id]
  · rw [comparisonPresentationHom_change, VariableChange.map_id]

end FLT.Mazur.WeierstrassChangeParameter
