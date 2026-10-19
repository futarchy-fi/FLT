/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GeneralizedCurveSquareTestTransport
public import FLT.Mazur.GeneralizedComparisonPullbackCoherence

/-!
# Full comparisons on tests of original-family charts

Restriction of a global comparison through a chart recovers the chart
comparison with the original base maps, even when the two families have
different original bases.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.GeneralizedEllipticCurve
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {S S' P A Q T : Scheme}
  (E : GeneralizedEllipticCurve S) (F : GeneralizedEllipticCurve S')

/-- Pull back a full comparison to independently specified original-family base maps. -/
def comparisonPullbackBetween (g : P ⟶ S) (j : P ⟶ S') (f : T ⟶ P)
    (q : T ⟶ S) (r : T ⟶ S') (hq : q = f ≫ g) (hr : r = f ≫ j)
    (e : E.baseChange g ≅ F.baseChange j) : E.baseChange q ≅ F.baseChange r :=
  E.baseChangeCompEqIso g f q hq ≪≫ (baseChangeFunctor f).mapIso e ≪≫
    (F.baseChangeCompEqIso j f r hr).symm

variable (g : P ⟶ S) (j : P ⟶ S') (u : Q ⟶ P)
  (q : A ⟶ S) (r : A ⟶ S') (s : Q ⟶ A)
  (wE : u ≫ g = s ≫ q) (wF : u ≫ j = s ≫ r)
  (k : T ⟶ Q) (t : T ⟶ A) (ht : t = k ≫ s)

/-- A chart's actual full comparison is recovered on every scheme test of that chart. -/
theorem comparisonPullbackBetween_chart
    (e : E.baseChange g ≅ F.baseChange j)
    (a : (E.baseChange q).baseChange s ≅ (F.baseChange r).baseChange s)
    (ha : (baseChangeFunctor u).mapIso e =
      E.baseChangeSquareIso g u q s wE ≪≫ a ≪≫
        (F.baseChangeSquareIso j u r s wF).symm) :
    comparisonPullbackBetween E F g j (k ≫ u) (t ≫ q) (t ≫ r)
        (squareTest_base g u q s wE k t ht) (squareTest_base j u r s wF k t ht) e =
      E.baseChangeCompIso q t ≪≫
        comparisonPullback (E.baseChange q) (F.baseChange r) s k t ht a ≪≫
          (F.baseChangeCompIso r t).symm := by
  let A := E.baseChangeCompEqIso g (k ≫ u) (t ≫ q)
    (squareTest_base g u q s wE k t ht)
  let B := F.baseChangeCompEqIso j (k ≫ u) (t ≫ r)
    (squareTest_base j u r s wF k t ht)
  let C := (E.baseChange g).baseChangeCompIso u k
  let D := (F.baseChange j).baseChangeCompIso u k
  let R := (baseChangeFunctor k).mapIso (E.baseChangeSquareIso g u q s wE)
  let V := (baseChangeFunctor k).mapIso (F.baseChangeSquareIso j u r s wF)
  let L := E.baseChangeCompIso q t ≪≫ (E.baseChange q).baseChangeCompEqIso s k t ht
  let N := F.baseChangeCompIso r t ≪≫ (F.baseChange r).baseChangeCompEqIso s k t ht
  have hE : A ≪≫ C ≪≫ R = L := E.baseChangeSquareIso_test g u q s wE k t ht
  have hF : B ≪≫ D ≪≫ V = N := F.baseChangeSquareIso_test j u r s wF k t ht
  have hn := (baseChangeComp u k).hom.naturality e.hom
  change baseChangeMap (k ≫ u) e.hom ≫ D.hom =
    C.hom ≫ baseChangeMap k (baseChangeMap u e.hom) at hn
  have hc := congrArg (fun z ↦ (baseChangeFunctor k).mapIso z) ha
  simp only [Functor.mapIso_trans, Functor.mapIso_symm] at hc
  have hl := congrArg Iso.hom hE
  have hr := congrArg Iso.hom hF
  change A.hom ≫ C.hom ≫ R.hom = L.hom at hl
  change B.hom ≫ D.hom ≫ V.hom = N.hom at hr
  suffices h : A ≪≫ (baseChangeFunctor (k ≫ u)).mapIso e ≪≫ B.symm =
      L ≪≫ (baseChangeFunctor k).mapIso a ≪≫ N.symm by
    apply Iso.ext
    have hh := congrArg Iso.hom h
    simpa only [A, B, L, N, comparisonPullbackBetween, comparisonPullback,
      Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Category.assoc] using hh
  apply Iso.ext
  apply (cancel_mono N.hom).mp
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.inv_hom_id,
    Category.comp_id]
  rw [← hr]
  simp only [Iso.inv_hom_id_assoc]
  change A.hom ≫ baseChangeMap (k ≫ u) e.hom ≫ D.hom ≫ V.hom =
    L.hom ≫ baseChangeMap k a.hom
  rw [← Category.assoc (baseChangeMap (k ≫ u) e.hom), hn]
  have hc' := congrArg Iso.hom hc
  change baseChangeMap k (baseChangeMap u e.hom) =
    R.hom ≫ baseChangeMap k a.hom ≫ V.inv at hc'
  rw [hc']
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [← hl]
  simp only [Category.assoc]

end FLT.Mazur.GeneralizedEllipticCurve
