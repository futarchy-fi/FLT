/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GeneralizedCurveSquareProjection

/-!
# Original-family transports on tests of a commuting square

The transport through a comparison chart agrees with the direct transport
from the original family, with independently named test base maps.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.GeneralizedEllipticCurve
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {S P A Q T : Scheme} (E : GeneralizedEllipticCurve S)
  (g : P ⟶ S) (u : Q ⟶ P) (q : A ⟶ S) (s : Q ⟶ A)
  (w : u ≫ g = s ≫ q) (k : T ⟶ Q) (t : T ⟶ A) (ht : t = k ≫ s)

include w ht in
/-- A test of a commuting square retains its original base map. -/
theorem squareTest_base : t ≫ q = (k ≫ u) ≫ g := by
  rw [ht, Category.assoc, ← w, ← Category.assoc]

/-- Both full transport paths to an iterated chart test agree. -/
theorem baseChangeSquareIso_test :
    E.baseChangeCompEqIso g (k ≫ u) (t ≫ q) (squareTest_base g u q s w k t ht) ≪≫
      (E.baseChange g).baseChangeCompIso u k ≪≫
        (baseChangeFunctor k).mapIso (E.baseChangeSquareIso g u q s w) =
    E.baseChangeCompIso q t ≪≫ (E.baseChange q).baseChangeCompEqIso s k t ht := by
  apply Iso.ext
  apply E.baseChange_thrice_hom_ext q s k
  change ((E.baseChangeCompEqIso g (k ≫ u) (t ≫ q) _).hom.curve.left ≫
    ((E.baseChange g).baseChangeCompIso u k).hom.curve.left ≫
      (baseChangeMap k (E.baseChangeSquareIso g u q s w).hom).curve.left) ≫ _ =
    ((E.baseChangeCompIso q t).hom.curve.left ≫
      ((E.baseChange q).baseChangeCompEqIso s k t ht).hom.curve.left) ≫ _
  simp only [Category.assoc, baseChangeMap_fst_assoc, baseChangeSquareIso_curve_fst,
    baseChangeCompIso_fst_fst_assoc, baseChangeCompEqIso_curve_fst,
    baseChangeCompEqIso_curve_fst_assoc, baseChangeCompIso_fst_fst]

end FLT.Mazur.GeneralizedEllipticCurve
