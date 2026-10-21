/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CompatibleSubgroupRefinementCast

/-!
# Extending compatible subgroup presentations

Changing the common presentation through a further pullback preserves the
actual compatible comparison, including its full curve and subgroup map.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.GeneralizedEllipticCurve.FiniteSubgroup
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {S T U V : Scheme} {n : ℕ} {E : GeneralizedEllipticCurve S}
  (H : E.FiniteSubgroup n) (p : T ⟶ S)
  {D : GeneralizedEllipticCurve T} {A : D.FiniteSubgroup n}
  (a : CompatibleIso A (H.baseChange p))

/-- Extend a subgroup presentation to the original family through a composite base map. -/
def compatiblePresentationExtension (q : U ⟶ T)
    {F : GeneralizedEllipticCurve U} {B : F.FiniteSubgroup n}
    (b : CompatibleIso B (A.baseChange q)) :
    CompatibleIso B (H.baseChange (q ≫ p)) :=
  b.trans ((a.baseChange q).trans (compatibleBaseChangeComp H p q).symm)

/-- Extending the common presentation leaves its full compatible transport unchanged. -/
theorem compatibleRefinementTransport_extension (q : U ⟶ T) (r : V ⟶ T)
    (f : V ⟶ U) (w : r = f ≫ q)
    {F : GeneralizedEllipticCurve U} {G : GeneralizedEllipticCurve V}
    {B : F.FiniteSubgroup n} {C : G.FiniteSubgroup n}
    (b : CompatibleIso B (A.baseChange q)) (c : CompatibleIso C (A.baseChange r)) :
    compatibleRefinementTransport H (q ≫ p) (r ≫ p) f
        (by rw [w, Category.assoc])
        (compatiblePresentationExtension H p a q b)
        (compatiblePresentationExtension H p a r c) =
      compatibleRefinementTransport A q r f w b c := by
  subst r
  symm
  apply compatibleRefinementTransport_unique
  simp only [compatiblePresentationExtension, CompatibleIso.baseChange_trans,
    CompatibleIso.baseChange_symm, CompatibleIso.trans_assoc]
  rw [← CompatibleIso.trans_assoc, compatibleRefinementTransport_presentation]
  change (c.trans (compatibleBaseChangeComp A q f)).trans _ = _
  rw [CompatibleIso.trans_assoc, ← CompatibleIso.trans_assoc
    (compatibleBaseChangeComp A q f), CompatibleIso.baseChange_comp_natural]
  simp only [CompatibleIso.trans_assoc]
  congr 2
  have hc := compatibleBaseChangeComp_assoc H p q f
  apply CompatibleIso.trans_right_cancel ((compatibleBaseChangeComp H p q).baseChange f)
  simp only [CompatibleIso.trans_assoc, CompatibleIso.symm_trans,
    CompatibleIso.trans_refl]
  rw [← hc, ← CompatibleIso.trans_assoc, CompatibleIso.symm_trans,
    CompatibleIso.refl_trans]

end FLT.Mazur.GeneralizedEllipticCurve.FiniteSubgroup
