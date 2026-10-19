/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CompatibleSubgroupBaseChangeCompEq
public import FLT.Mazur.GeneralizedComparisonPullbackCoherence

/-!
# Compatible subgroup refinements on a comparison parameter scheme

Coherent base maps transport the entire refined subgroup to the pullback
of the original parameter family. Full comparison identities survive this transport.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.GeneralizedEllipticCurve.FiniteSubgroup
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {S T U V : Scheme} {n : ℕ}
  (s : T ⟶ S) (p : V ⟶ T) (k : U ⟶ S) (t : V ⟶ U) (v : V ⟶ S)
  (hp : v = p ≫ s) (ht : v = t ≫ k)
  {E F : GeneralizedEllipticCurve S} {E' F' : GeneralizedEllipticCurve U}
  {H : E.FiniteSubgroup n} {J : F.FiniteSubgroup n}
  {H' : E'.FiniteSubgroup n} {J' : F'.FiniteSubgroup n}
  (a : CompatibleIso H' (H.baseChange k)) (b : CompatibleIso J' (J.baseChange k))

/-- The refined parameter family compares compatibly with the original parameter pullback. -/
def compatibleParameterRefinement :
    CompatibleIso (H'.baseChange t) ((H.baseChange s).baseChange p) :=
  (a.baseChange t).trans ((compatibleBaseChangeCompEq H k t v ht).symm.trans
    (compatibleBaseChangeCompEq H s p v hp))

/-- Its full curve is the exact prescribed refinement square. -/
theorem compatibleParameterRefinement_curve :
    (compatibleParameterRefinement s p k t v hp ht a).curve =
      (baseChangeFunctor t).mapIso a.curve ≪≫ (E.baseChangeCompEqIso k t v ht).symm ≪≫
        E.baseChangeCompEqIso s p v hp := by
  simp only [compatibleParameterRefinement, CompatibleIso.trans, CompatibleIso.symm,
    CompatibleIso.baseChange, compatibleBaseChangeCompEq_curve]

/-- A full refinement identity is precisely conjugation through the compatible transports. -/
theorem compatibleParameterRefinement_conjugate
    (e : E.baseChange s ≅ F.baseChange s) (e' : E'.baseChange t ≅ F'.baseChange t)
    (he : comparisonPullback E F s p v hp e =
      E.baseChangeCompEqIso k t v ht ≪≫ ((baseChangeFunctor t).mapIso a.curve).symm ≪≫
        e' ≪≫ (baseChangeFunctor t).mapIso b.curve ≪≫
          (F.baseChangeCompEqIso k t v ht).symm) :
    e' = (compatibleParameterRefinement s p k t v hp ht a).curve ≪≫
      (baseChangeFunctor p).mapIso e ≪≫
        (compatibleParameterRefinement s p k t v hp ht b).curve.symm := by
  rw [compatibleParameterRefinement_curve, compatibleParameterRefinement_curve]
  have h := congrArg (fun z ↦
    (baseChangeFunctor t).mapIso a.curve ≪≫ (E.baseChangeCompEqIso k t v ht).symm ≪≫
      z ≪≫ F.baseChangeCompEqIso k t v ht ≪≫
        ((baseChangeFunctor t).mapIso b.curve).symm) he
  simp only [Iso.trans_assoc, Iso.symm_self_id_assoc, Iso.self_symm_id_assoc,
    Iso.self_symm_id, Iso.trans_refl] at h
  rw [← h]
  apply Iso.ext
  simp only [comparisonPullback, Iso.trans_hom, Iso.trans_inv, Iso.symm_hom,
    Iso.symm_inv, Category.assoc]

end FLT.Mazur.GeneralizedEllipticCurve.FiniteSubgroup
