/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeOpenPairSectionRestriction

/-!
# Action-overlap equations from original relation graphs

If an automorphism graph is an actual arrow into the original relation,
its open overlap equation follows from the full pair equation. No
separate invariance assumption on the section is needed.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.SchemeFiniteGroupQuotient
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {X D : Scheme} (f g : D ⟶ X) (a : X ⟶ X)
  (r : X ⟶ D) (hrf : r ≫ f = 𝟙 X) (hrg : r ≫ g = a)

include hrf hrg in
/-- Restricting an original relation graph derives the translate-overlap equation. -/
theorem pairOpen_equation_of_relation_graph (O : X.Opens) (v : Γ(O.toScheme, ⊤))
    (hv : (pairOpenFirst O f g).appTop v = (pairOpenSecond O f g).appTop v) :
    (pairOpenFirst O (𝟙 X) a).appTop v = (pairOpenSecond O (𝟙 X) a).appTop v := by
  apply pairOpen_equation_pullback O f g v hv
    ((pairOpenDomain O (𝟙 X) a).ι ≫ r)
    (pairOpenFirst O (𝟙 X) a) (pairOpenSecond O (𝟙 X) a)
  · simp only [pairOpenFirst, Scheme.Hom.resLE_comp_ι, Category.assoc, hrf]
  · simp only [pairOpenSecond, Scheme.Hom.resLE_comp_ι, Category.assoc, hrg]

end FLT.Mazur.SchemeFiniteGroupQuotient
