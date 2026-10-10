/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.AlgebraicGeometry.AffineTransitionLimit

/-!
# Inclusions between restricted inverse systems

Inclusions of fixed opens commute with every transition and every limit
projection. These squares give restriction maps between the section colimits.
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry

namespace FLT.Mazur.Approximation

universe u

variable {I : Type u} [Category.{u} I] (D : I ⥤ Scheme.{u})
  (i : I) {U V : (D.obj i).Opens}

/-- Inclusion of fixed opens gives a natural inclusion of their inverse systems. -/
def opensDiagramInclusion (h : U ≤ V) : opensDiagram D i U ⟶ opensDiagram D i V where
  app j := (D.obj j.left).homOfLE ((D.map j.hom).preimage_mono h)
  naturality {j k} f := by
    apply (cancel_mono (D.map k.hom ⁻¹ᵁ V).ι).mp
    change ((D.map f.left).resLE _ _ _ ≫ (D.obj k.left).homOfLE _) ≫ _ =
      ((D.obj j.left).homOfLE _ ≫ (D.map f.left).resLE _ _ _) ≫ _
    simp only [Category.assoc, Scheme.homOfLE_ι, Scheme.homOfLE_ι_assoc,
      Scheme.Hom.resLE_comp_ι]

/-- The limit projections commute with inclusions of fixed opens. -/
@[reassoc] theorem opensCone_inclusion (c : Cone D) (h : U ≤ V) (j : Over i) :
    (opensCone D c i U).π.app j ≫ (opensDiagramInclusion D i h).app j =
      c.pt.homOfLE ((c.π.app i).preimage_mono h) ≫ (opensCone D c i V).π.app j := by
  apply (cancel_mono (D.map j.hom ⁻¹ᵁ V).ι).mp
  change ((c.π.app j.left).resLE _ _ _ ≫ (D.obj j.left).homOfLE
      ((D.map j.hom).preimage_mono h)) ≫ _ =
    (c.pt.homOfLE ((c.π.app i).preimage_mono h) ≫ (c.π.app j.left).resLE _ _ _) ≫ _
  simp only [Category.assoc, Scheme.homOfLE_ι, Scheme.homOfLE_ι_assoc,
      Scheme.Hom.resLE_comp_ι]

end FLT.Mazur.Approximation
