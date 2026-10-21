/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CompatibleSubgroupRefinementTransport

/-!
# Unit coherence for compatible subgroup refinement

The identity refinement is the canonical inverse identity pullback comparison.
This equality retains the full curve and the actual subgroup inclusion.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.GeneralizedEllipticCurve.FiniteSubgroup
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {S T : Scheme} {n : ℕ} {E : GeneralizedEllipticCurve S}
  (H : E.FiniteSubgroup n) (p : T ⟶ S)

/-- The compatible identity pullback comparison is natural in full subgroup isomorphisms. -/
theorem CompatibleIso.baseChange_id_natural {F : GeneralizedEllipticCurve S}
    {J : F.FiniteSubgroup n} (a : CompatibleIso H J) :
    (a.baseChange (𝟙 S)).trans (compatibleBaseChangeId J) =
      (compatibleBaseChangeId H).trans a := by
  apply CompatibleIso.ext_curve_hom
  exact GeneralizedEllipticCurve.baseChangeId.hom.naturality a.curve.hom

/-- The equal-composite comparison satisfies the actual subgroup unit law. -/
theorem compatibleBaseChangeCompEq_id :
    (compatibleBaseChangeCompEq H p (𝟙 T) p (Category.id_comp p).symm).trans
      (compatibleBaseChangeId (H.baseChange p)) = CompatibleIso.refl (H.baseChange p) := by
  apply CompatibleIso.ext_curve_hom
  change (compatibleBaseChangeCompEq H p (𝟙 T) p _).curve.hom ≫
    (E.baseChange p).baseChangeIdIso.hom = 𝟙 _
  rw [compatibleBaseChangeCompEq_curve]
  apply baseChange_hom_ext p
  change ((E.baseChangeCompEqIso p (𝟙 T) p _).hom.curve.left ≫
    (E.baseChange p).baseChangeIdIso.hom.curve.left) ≫ pullback.fst E.curve.hom p =
      (𝟙 _) ≫ pullback.fst E.curve.hom p
  rw [Category.assoc, baseChangeIdIso_left]
  exact (baseChangeCompEqIso_curve_fst E p (𝟙 T) p _).trans (Category.id_comp _).symm

/-- Refining a presentation by the identity gives the canonical identity pullback isomorphism. -/
theorem compatibleRefinementTransport_id {D : GeneralizedEllipticCurve T}
    {A : D.FiniteSubgroup n} (a : CompatibleIso A (H.baseChange p)) :
    compatibleRefinementTransport H p p (𝟙 T) (Category.id_comp p).symm a a =
      (compatibleBaseChangeId A).symm := by
  symm
  apply compatibleRefinementTransport_unique
  have h := CompatibleIso.baseChange_id_natural A a
  have u := compatibleBaseChangeCompEq_id H p
  apply CompatibleIso.ext_curve_hom
  have hc := congrArg (fun z ↦ z.curve.hom) h
  have hu := congrArg (fun z ↦ z.curve.hom) u
  change (baseChangeFunctor (𝟙 T)).map a.curve.hom ≫
    (E.baseChange p).baseChangeIdIso.hom = D.baseChangeIdIso.hom ≫ a.curve.hom at hc
  change (compatibleBaseChangeCompEq H p (𝟙 T) p _).curve.hom ≫
    (E.baseChange p).baseChangeIdIso.hom = 𝟙 _ at hu
  change D.baseChangeIdIso.inv ≫ (baseChangeFunctor (𝟙 T)).map a.curve.hom =
    a.curve.hom ≫ (compatibleBaseChangeCompEq H p (𝟙 T) p _).curve.hom
  apply (cancel_mono (E.baseChange p).baseChangeIdIso.hom).mp
  rw [Category.assoc, hc, Iso.inv_hom_id_assoc, Category.assoc, hu, Category.comp_id]

end FLT.Mazur.GeneralizedEllipticCurve.FiniteSubgroup
