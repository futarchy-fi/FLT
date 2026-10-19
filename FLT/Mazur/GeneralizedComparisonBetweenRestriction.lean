/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GeneralizedComparisonSquareTest
public import FLT.Mazur.GeneralizedPresentationRefinement

/-!
# Restriction of comparisons between families with different original bases

Direct and iterated tests retain the same full comparison. The original
left and right base maps remain explicit throughout both transport paths.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.GeneralizedEllipticCurve
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {S S' P Q T : Scheme}
  (E : GeneralizedEllipticCurve S) (F : GeneralizedEllipticCurve S')
  (g : P ⟶ S) (j : P ⟶ S') (u : Q ⟶ P) (k : T ⟶ Q)
  (q : T ⟶ S) (r : T ⟶ S')
  (hq : q = (k ≫ u) ≫ g) (hr : r = (k ≫ u) ≫ j)

/-- Two literal pullbacks of the full comparison equal its pullback along the composite. -/
theorem comparisonPullbackBetween_iterated (e : E.baseChange g ≅ F.baseChange j) :
    E.baseChangeCompEqIso g (k ≫ u) q hq ≪≫
      (E.baseChange g).baseChangeCompIso u k ≪≫
        (baseChangeFunctor k).mapIso ((baseChangeFunctor u).mapIso e) ≪≫
          ((F.baseChange j).baseChangeCompIso u k).symm ≪≫
            (F.baseChangeCompEqIso j (k ≫ u) r hr).symm =
      comparisonPullbackBetween E F g j (k ≫ u) q r hq hr e := by
  have hn := (baseChangeComp u k).hom.naturality e.hom
  change baseChangeMap (k ≫ u) e.hom ≫ ((F.baseChange j).baseChangeCompIso u k).hom =
    ((E.baseChange g).baseChangeCompIso u k).hom ≫
      baseChangeMap k (baseChangeMap u e.hom) at hn
  apply Iso.ext
  change (E.baseChangeCompEqIso g (k ≫ u) q hq).hom ≫
    ((E.baseChange g).baseChangeCompIso u k).hom ≫
      baseChangeMap k (baseChangeMap u e.hom) ≫
        ((F.baseChange j).baseChangeCompIso u k).inv ≫
          (F.baseChangeCompEqIso j (k ≫ u) r hr).inv =
    (E.baseChangeCompEqIso g (k ≫ u) q hq).hom ≫ baseChangeMap (k ≫ u) e.hom ≫
      (F.baseChangeCompEqIso j (k ≫ u) r hr).inv
  rw [← Category.assoc ((E.baseChange g).baseChangeCompIso u k).hom, ← hn]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]

variable (v : Q ⟶ S) (w : Q ⟶ S') (hv : v = u ≫ g) (hw : w = u ≫ j)
  (hqt : q = k ≫ v) (hrt : r = k ≫ w)

/-- Restriction with newly named original bases agrees with the composite parameter map. -/
theorem comparisonPullbackBetween_restrict (e : E.baseChange g ≅ F.baseChange j) :
    comparisonPullbackBetween E F v w k q r hqt hrt
        (comparisonPullbackBetween E F g j u v w hv hw e) =
      comparisonPullbackBetween E F g j (k ≫ u) q r
        (hqt.trans ((congrArg (k ≫ ·) hv).trans (Category.assoc k u g).symm))
        (hrt.trans ((congrArg (k ≫ ·) hw).trans (Category.assoc k u j).symm)) e := by
  let A := E.baseChangeCompEqIso g (k ≫ u) q
    (hqt.trans ((congrArg (k ≫ ·) hv).trans (Category.assoc k u g).symm))
  let B := F.baseChangeCompEqIso j (k ≫ u) r
    (hrt.trans ((congrArg (k ≫ ·) hw).trans (Category.assoc k u j).symm))
  let C := E.baseChangeCompEqIso v k q hqt
  let D := F.baseChangeCompEqIso w k r hrt
  let L := (baseChangeFunctor k).mapIso (E.baseChangeCompEqIso g u v hv)
  let R := (baseChangeFunctor k).mapIso (F.baseChangeCompEqIso j u w hw)
  have hE : C.hom ≫ L.hom = A.hom ≫ ((E.baseChange g).baseChangeCompIso u k).hom :=
    (E.baseChangeCompEqIso_assoc g u k v q hv hqt).symm
  have hF : D.hom ≫ R.hom = B.hom ≫ ((F.baseChange j).baseChangeCompIso u k).hom :=
    (F.baseChangeCompEqIso_assoc j u k w r hw hrt).symm
  have hn := (baseChangeComp u k).hom.naturality e.hom
  change baseChangeMap (k ≫ u) e.hom ≫ ((F.baseChange j).baseChangeCompIso u k).hom =
    ((E.baseChange g).baseChangeCompIso u k).hom ≫
      baseChangeMap k (baseChangeMap u e.hom) at hn
  simp only [comparisonPullbackBetween, Functor.mapIso_trans, Functor.mapIso_symm]
  apply Iso.ext
  apply (cancel_mono (D.hom ≫ R.hom)).mp
  change (C.hom ≫ (L.hom ≫ baseChangeMap k (baseChangeMap u e.hom) ≫ R.inv) ≫ D.inv) ≫
    (D.hom ≫ R.hom) = (A.hom ≫ baseChangeMap (k ≫ u) e.hom ≫ B.inv) ≫ _
  simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id]
  rw [hF]
  simp only [Iso.inv_hom_id_assoc]
  rw [← Category.assoc C.hom, hE]
  simp only [Category.assoc]
  rw [hn]

end FLT.Mazur.GeneralizedEllipticCurve
