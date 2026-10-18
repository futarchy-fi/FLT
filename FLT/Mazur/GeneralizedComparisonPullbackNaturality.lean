/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GeneralizedComparisonPullbackCoherence

/-!
# Pullback of full comparisons respects original-family presentations

Transporting the universal comparison to an isomorphic original family
commutes with restriction to a test scheme. All equal-base-map transports
are retained in the full generalized-curve category.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.GeneralizedEllipticCurve
set_option backward.isDefEq.respectTransparency false
variable {S T U : Scheme} (s : T ⟶ S) (p : U ⟶ T) (t : U ⟶ S)
  (ht : t = p ≫ s)

/-- Equal-composite full pullback comparisons are natural in the original family. -/
theorem baseChangeCompEqIso_natural {E F : GeneralizedEllipticCurve S} (a : E ⟶ F) :
    baseChangeMap t a ≫ (F.baseChangeCompEqIso s p t ht).hom =
      (E.baseChangeCompEqIso s p t ht).hom ≫ baseChangeMap p (baseChangeMap s a) :=
  ((baseChangeCongr ht ≪≫ baseChangeComp s p).hom.naturality a)

/-- Pulling back the universal comparison commutes with transport to the original full models. -/
theorem comparisonPullback_natural
    {E F E' F' : GeneralizedEllipticCurve S} (a : E ≅ E') (b : F ≅ F')
    (e : E.baseChange s ≅ F.baseChange s) :
    comparisonPullback E' F' s p t ht
      (((baseChangeFunctor s).mapIso a).symm ≪≫ e ≪≫ (baseChangeFunctor s).mapIso b) =
    ((baseChangeFunctor t).mapIso a).symm ≪≫ comparisonPullback E F s p t ht e ≪≫
      (baseChangeFunctor t).mapIso b := by
  apply comparisonPullback_conjugate
    (r := E.baseChangeCompEqIso s p t ht) (q := F.baseChangeCompEqIso s p t ht)
  · exact baseChangeCompEqIso_natural s p t ht a.hom
  · exact baseChangeCompEqIso_natural s p t ht b.hom
  · simp only [comparisonPullback, Iso.trans_hom, Iso.symm_hom,
      Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rfl

end FLT.Mazur.GeneralizedEllipticCurve
