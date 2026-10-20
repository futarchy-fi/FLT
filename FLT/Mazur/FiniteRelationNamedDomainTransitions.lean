/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteEtaleInvariantDomainCoefficients

/-!
# Cartesian full relation maps on named invariant domains

Keep the same domain at each order while retaining both independent endpoints
and the cartesian first-endpoint square. No equality transport of schemes is
needed to compute the source map.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.FiniteRelationNamedDomainTransitions
set_option backward.isDefEq.respectTransparency false
variable {D A D' A' : Scheme.{0}} (p q : D ⟶ A) (p' q' : D' ⟶ A')
  (a : A' ⟶ A) (b : D' ⟶ D) (H : IsPullback b p' p a) (hq : b ≫ q = q' ≫ a)
  (U : A.Opens) (V : A'.Opens) (hU : p ⁻¹ᵁ U = q ⁻¹ᵁ U)
  (hV : p' ⁻¹ᵁ V = q' ⁻¹ᵁ V) (hUV : V = a ⁻¹ᵁ U)

include H hUV in
/-- The full lower arrow domain lies over the chosen full higher arrow domain. -/
theorem domain_le : p' ⁻¹ᵁ V ≤ b ⁻¹ᵁ (p ⁻¹ᵁ U) := by
  rw [hUV, ← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, H.w]

/-- Restrict the entire transition arrow to the fixed named domains. -/
def arrow : (p' ⁻¹ᵁ V).toScheme ⟶ (p ⁻¹ᵁ U).toScheme :=
  b.resLE _ _ (domain_le p p' a b H U V hUV)

/-- The named source map preserves the complete first endpoint. -/
@[reassoc]
theorem arrow_first : arrow p p' a b H U V hUV ≫ p.resLE U _ le_rfl =
    p'.resLE V _ le_rfl ≫ a.resLE U V hUV.le := by
  apply (cancel_mono U.ι).mp
  simp only [Category.assoc, Scheme.Hom.resLE_comp_ι,
    Scheme.Hom.resLE_comp_ι_assoc, arrow, H.w]

include hq in
/-- The same named source map preserves the independent second endpoint. -/
@[reassoc]
theorem arrow_second : arrow p p' a b H U V hUV ≫ q.resLE U _ hU.le =
    q'.resLE V _ hV.le ≫ a.resLE U V hUV.le := by
  apply (cancel_mono U.ι).mp
  simp only [Category.assoc, Scheme.Hom.resLE_comp_ι,
    Scheme.Hom.resLE_comp_ι_assoc, arrow, hq]

/-- The named full relation square is cartesian. -/
theorem arrow_isPullback : IsPullback (arrow p p' a b H U V hUV)
    (p'.resLE V _ le_rfl) (p.resLE U _ le_rfl) (a.resLE U V hUV.le) := by
  apply IsPullback.of_right _ (arrow_first p p' a b H U V hUV)
    (by rw [Scheme.Hom.resLE_eq_morphismRestrict]
        exact (isPullback_morphismRestrict p U).flip)
  rw [arrow, Scheme.Hom.resLE_comp_ι, Scheme.Hom.resLE_comp_ι]
  have H' : IsPullback (p' ⁻¹ᵁ V).ι (p'.resLE V _ le_rfl) p' V.ι := by
    rw [Scheme.Hom.resLE_eq_morphismRestrict]
    exact (isPullback_morphismRestrict p' V).flip
  exact H'.paste_horiz H

/-- Exact inverse-image domains preserve closedness of the original transition. -/
theorem source_closed [IsClosedImmersion a] : IsClosedImmersion (a.resLE U V hUV.le) := by
  subst V
  rw [Scheme.Hom.resLE_eq_morphismRestrict]
  infer_instance

end FLT.Mazur.FiniteRelationNamedDomainTransitions
