/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GroupMarkingFullTorsionRelabel
public import FLT.Mazur.UniversalWeierstrassAuxiliaryGeometricFull

/-!
# Auxiliary relabeling induced by the actual geometric group comparison

Every geometric isomorphism of the original pulled-back groups uniquely
matches their entire auxiliary frames, preserving the original sections.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry MonoidalCategory MonObj
open scoped CategoryTheory.Obj
namespace FLT.Mazur.UniversalWeierstrass
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {K : Type} [Field K] [IsAlgClosed K]
  (f g : Spec (.of K) ⟶ levelFour.left)

/-- The given geometric group comparison determines every auxiliary label uniquely. -/
theorem auxiliarySchemeMarking_geometric_relabel
    (e : auxiliarySchemeGroup f ≅ auxiliarySchemeGroup g) :
    ∃! r : MulAut (Labels 4), ∀ a,
      auxiliarySchemeMarking f (r a) ≫ e.hom.hom.hom.hom = auxiliarySchemeMarking g a := by
  exact GroupMarkingTransport.existsUnique_full_torsion_relabel _ _ e _ 4
    (auxiliarySchemeMarking f) (auxiliarySchemeMarking g)
    (auxiliarySchemeMarking_injective f) (auxiliarySchemeMarking_injective g)
    (auxiliarySchemeMarking_pow f) (auxiliarySchemeMarking_pow g)
    (fun P hP ↦ (auxiliarySchemeMarking_geometric_full f P hP).exists)
    (fun P hP ↦ (auxiliarySchemeMarking_geometric_full g P hP).exists)

end FLT.Mazur.UniversalWeierstrass
