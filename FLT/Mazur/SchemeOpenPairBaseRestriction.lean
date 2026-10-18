/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeOpenPairPrincipalRestriction

/-!
# Pulling back common-open relation equations to actual tests

Every map to the original relation induces a map on the domains where both
endpoints lie in the usable open. The two endpoint squares commute, so
compatible functions remain compatible on each affine covering test.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.SchemeFiniteGroupQuotient
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {X Z T : Scheme} (O : X.Opens) (f g : Z ⟶ X) (a : T ⟶ Z)

/-- The actual induced map of the common usable relation domains. -/
def pairOpenBaseMap :
    (pairOpenDomain O (a ≫ f) (a ≫ g)).toScheme ⟶ (pairOpenDomain O f g).toScheme :=
  a.resLE _ _ (by
    simp only [pairOpenDomain, Scheme.Hom.comp_preimage, Scheme.Hom.preimage_inf]
    exact le_rfl)

/-- Pullback of the common-open relation keeps its first original endpoint. -/
@[reassoc] theorem pairOpenBaseMap_first :
    pairOpenBaseMap O f g a ≫ pairOpenFirst O f g = pairOpenFirst O (a ≫ f) (a ≫ g) := by
  apply (cancel_mono O.ι).mp
  simp only [pairOpenBaseMap, pairOpenFirst, Category.assoc,
    Scheme.Hom.resLE_comp_ι, Scheme.Hom.resLE_comp_ι_assoc]

/-- Pullback of the common-open relation keeps its second original endpoint. -/
@[reassoc] theorem pairOpenBaseMap_second :
    pairOpenBaseMap O f g a ≫ pairOpenSecond O f g = pairOpenSecond O (a ≫ f) (a ≫ g) := by
  apply (cancel_mono O.ι).mp
  simp only [pairOpenBaseMap, pairOpenSecond, Category.assoc,
    Scheme.Hom.resLE_comp_ι, Scheme.Hom.resLE_comp_ι_assoc]

/-- An equation on the full usable relation implies the exact equation on every covering test. -/
theorem pairOpen_equation_base (v : Γ(O.toScheme, ⊤))
    (he : (pairOpenFirst O f g).appTop v = (pairOpenSecond O f g).appTop v) :
    (pairOpenFirst O (a ≫ f) (a ≫ g)).appTop v =
      (pairOpenSecond O (a ≫ f) (a ≫ g)).appTop v := by
  have h := congrArg (fun t ↦ (pairOpenBaseMap O f g a).appTop t) he
  change (pairOpenBaseMap O f g a ≫ pairOpenFirst O f g).appTop v =
    (pairOpenBaseMap O f g a ≫ pairOpenSecond O f g).appTop v at h
  simpa only [pairOpenBaseMap_first, pairOpenBaseMap_second] using h

end FLT.Mazur.SchemeFiniteGroupQuotient
