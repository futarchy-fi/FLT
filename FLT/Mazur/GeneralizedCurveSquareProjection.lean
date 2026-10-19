/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GeneralizedCurveIteratedProjection

/-!
# Full curve comparisons around commuting base squares

The canonical square comparison preserves the original curve projection.
This determines its coherence with any refinement preserving that projection.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.GeneralizedEllipticCurve
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {S P A B Q R : Scheme} (E : GeneralizedEllipticCurve S)

/-- Transport between two iterated pullbacks with the same original base map. -/
def baseChangeSquareIso (g : P ⟶ S) (u : Q ⟶ P) (q : A ⟶ S) (s : Q ⟶ A)
    (w : u ≫ g = s ≫ q) : (E.baseChange g).baseChange u ≅
      (E.baseChange q).baseChange s :=
  (E.baseChangeCompIso g u).symm ≪≫ E.baseChangeCompEqIso q s (u ≫ g) w

/-- A square comparison retains the projection to the original curve. -/
@[reassoc] theorem baseChangeSquareIso_curve_fst
    (g : P ⟶ S) (u : Q ⟶ P) (q : A ⟶ S) (s : Q ⟶ A) (w : u ≫ g = s ≫ q) :
    (E.baseChangeSquareIso g u q s w).hom.curve.left ≫
      pullback.fst _ s ≫ pullback.fst E.curve.hom q =
        pullback.fst _ u ≫ pullback.fst E.curve.hom g := by
  change ((E.baseChangeCompIso g u).inv.curve.left ≫
    (E.baseChangeCompEqIso q s (u ≫ g) w).hom.curve.left) ≫ _ = _
  rw [Category.assoc, baseChangeCompEqIso_curve_fst, baseChangeCompIso_inv_curve_fst]

/-- Original-coordinate preservation forces coherence of the full square transports. -/
theorem baseChangeSquareIso_refine
    (g : P ⟶ S) (u : Q ⟶ P) (v : R ⟶ P) (m : Q ⟶ R)
    (q : A ⟶ S) (s : R ⟶ A) (q' : B ⟶ S) (t : Q ⟶ B)
    (hu : u ≫ g = t ≫ q') (hv : v ≫ g = s ≫ q) (hm : u = m ≫ v)
    (a : (E.baseChange q').baseChange t ≅ ((E.baseChange q).baseChange s).baseChange m)
    (ha : a.hom.curve.left ≫ pullback.fst _ m ≫ pullback.fst _ s ≫
      pullback.fst E.curve.hom q = pullback.fst _ t ≫ pullback.fst E.curve.hom q') :
    E.baseChangeSquareIso g u q' t hu ≪≫ a =
      (E.baseChange g).baseChangeCompEqIso v m u hm ≪≫
        (baseChangeFunctor m).mapIso (E.baseChangeSquareIso g v q s hv) := by
  apply Iso.ext
  apply E.baseChange_thrice_hom_ext q s m
  change ((E.baseChangeSquareIso g u q' t hu).hom.curve.left ≫ a.hom.curve.left) ≫ _ =
    (((E.baseChange g).baseChangeCompEqIso v m u hm).hom.curve.left ≫
      (baseChangeMap m (E.baseChangeSquareIso g v q s hv).hom).curve.left) ≫ _
  simp only [Category.assoc, ha, baseChangeSquareIso_curve_fst, baseChangeMap_fst_assoc,
    baseChangeCompEqIso_curve_fst_assoc]

end FLT.Mazur.GeneralizedEllipticCurve
