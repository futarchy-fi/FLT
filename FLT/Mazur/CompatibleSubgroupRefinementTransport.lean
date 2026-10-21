/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CompatibleSubgroupBaseChangeCoherence

/-!
# Compatible transport between two presentations of one subgroup

A commuting triangle of parameter schemes transports the entire subgroup,
including its full curve. The comparison is characterized by its compatibility
with the two supplied presentations, rather than by equality of modular classes.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.GeneralizedEllipticCurve.FiniteSubgroup
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {S T U : Scheme} {n : ℕ} {E : GeneralizedEllipticCurve S}
  (H : E.FiniteSubgroup n) (p : T ⟶ S) (q : U ⟶ S) (f : U ⟶ T) (w : q = f ≫ p)
  {D : GeneralizedEllipticCurve T} {F : GeneralizedEllipticCurve U}
  {A : D.FiniteSubgroup n} {B : F.FiniteSubgroup n}
  (a : CompatibleIso A (H.baseChange p)) (b : CompatibleIso B (H.baseChange q))

/-- The actual compatible comparison induced by two presentations and a base triangle. -/
def compatibleRefinementTransport : CompatibleIso B (A.baseChange f) :=
  b.trans ((compatibleBaseChangeCompEq H p f q w).trans (a.baseChange f).symm)

/-- Transport commutes with the supplied presentations as actual compatible isomorphisms. -/
theorem compatibleRefinementTransport_presentation :
    (compatibleRefinementTransport H p q f w a b).trans (a.baseChange f) =
      b.trans (compatibleBaseChangeCompEq H p f q w) := by
  simp only [compatibleRefinementTransport, CompatibleIso.trans_assoc,
    CompatibleIso.symm_trans, CompatibleIso.trans_refl]

/-- The presentation square determines the entire compatible subgroup comparison uniquely. -/
theorem compatibleRefinementTransport_unique (c : CompatibleIso B (A.baseChange f))
    (hc : c.trans (a.baseChange f) = b.trans (compatibleBaseChangeCompEq H p f q w)) :
    c = compatibleRefinementTransport H p q f w a b := by
  have h := congrArg (fun z ↦ z.trans (a.baseChange f).symm) hc
  simpa only [CompatibleIso.trans_assoc, CompatibleIso.trans_symm,
    CompatibleIso.trans_refl, compatibleRefinementTransport] using h

/-- The full curve of transport is the canonical conjugate of the pullback comparison. -/
theorem compatibleRefinementTransport_curve :
    (compatibleRefinementTransport H p q f w a b).curve =
      b.curve ≪≫ E.baseChangeCompEqIso p f q w ≪≫
        ((baseChangeFunctor f).mapIso a.curve).symm := by
  simp only [compatibleRefinementTransport, CompatibleIso.trans, CompatibleIso.symm,
    CompatibleIso.baseChange, compatibleBaseChangeCompEq_curve]

end FLT.Mazur.GeneralizedEllipticCurve.FiniteSubgroup
