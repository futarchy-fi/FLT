/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeRelationInvariantRestriction

/-!
# The full relation on a saturated open is a single open restriction

When the two endpoint inverse images agree, retaining both endpoints does not
discard any arrows above the open. Construct the actual scheme isomorphism
between the full double pullback and that single open in the original relation.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace FLT.Mazur.SchemeRelationRestriction
set_option backward.isDefEq.respectTransparency false
variable {D A : Scheme.{u}} (p q : D ⟶ A) (W : A.Opens)
  (hW : p ⁻¹ᵁ W = q ⁻¹ᵁ W)

/-- Both endpoints of every original arrow above the invariant open lift to that open. -/
def fromInvariantDomain : (p ⁻¹ᵁ W).toScheme ⟶ doubleDomain p q W.ι :=
  lift p q W.ι (p ⁻¹ᵁ W).ι (p.resLE W (p ⁻¹ᵁ W) le_rfl)
    (q.resLE W (p ⁻¹ᵁ W) hW.le) (Scheme.Hom.resLE_comp_ι p le_rfl).symm
    (Scheme.Hom.resLE_comp_ι q hW.le).symm

@[reassoc]
theorem fromInvariantDomain_arrow : fromInvariantDomain p q W hW ≫ arrow p q W.ι =
    (p ⁻¹ᵁ W).ι := lift_arrow _ _ _ _ _ _ _ _

/-- The full double pullback is exactly the original open relation domain. -/
def invariantDomainIso : doubleDomain p q W.ι ≅ (p ⁻¹ᵁ W).toScheme where
  hom := toInvariantDomain p q W
  inv := fromInvariantDomain p q W hW
  hom_inv_id := by
    apply pullback.hom_ext
    · apply pullback.hom_ext
      · change toInvariantDomain p q W ≫ fromInvariantDomain p q W hW ≫
          arrow p q W.ι = arrow p q W.ι
        rw [fromInvariantDomain_arrow, toInvariantDomain_arrow]
      · change toInvariantDomain p q W ≫ fromInvariantDomain p q W hW ≫
          fst p q W.ι = fst p q W.ι
        rw [fromInvariantDomain, lift_fst, toInvariantDomain_fst]
    · change toInvariantDomain p q W ≫ fromInvariantDomain p q W hW ≫
        snd p q W.ι = snd p q W.ι
      rw [fromInvariantDomain, lift_snd, toInvariantDomain_snd p q W hW]
  inv_hom_id := by
    apply (cancel_mono (p ⁻¹ᵁ W).ι).mp
    rw [Category.assoc, toInvariantDomain_arrow, fromInvariantDomain_arrow, Category.id_comp]

/-- The isomorphism's original arrow is literally the open inclusion. -/
@[reassoc]
theorem invariantDomainIso_hom_ι : (invariantDomainIso p q W hW).hom ≫ (p ⁻¹ᵁ W).ι =
    arrow p q W.ι := toInvariantDomain_arrow p q W

include hW in
/-- Restriction to a saturated source is an open immersion of entire relation schemes. -/
theorem invariantDomain_arrow_isOpenImmersion : IsOpenImmersion (arrow p q W.ι) := by
  rw [← invariantDomainIso_hom_ι p q W hW]
  infer_instance

end FLT.Mazur.SchemeRelationRestriction
