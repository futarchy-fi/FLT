/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CompatibleSubgroupRefinementComposition
public import FLT.Mazur.CompatibleSubgroupRefinementUnits

/-!
# Identifying comparisons constructed by rewriting a parameter equation

The existing boundary comparisons rewrite their original-parameter equations
inside an iterated pullback. This identifies that construction with the
presentation transport, so its coherence applies to the original comparisons.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.GeneralizedEllipticCurve.FiniteSubgroup
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {S T U : Scheme} {n : ℕ} {E : GeneralizedEllipticCurve S}
  (H : E.FiniteSubgroup n) (p : T ⟶ S) (q : U ⟶ S) (f : U ⟶ T) (w : f ≫ p = q)
  {D : GeneralizedEllipticCurve T} {F : GeneralizedEllipticCurve U}
  {A : D.FiniteSubgroup n} {B : F.FiniteSubgroup n}
  (a : CompatibleIso A (H.baseChange p)) (b : CompatibleIso B (H.baseChange q))

/-- Rewriting the parameter equation gives exactly the canonical full subgroup transport. -/
theorem compatibleRefinementTransport_cast :
    (by
      let c := (a.baseChange f).trans (compatibleBaseChangeComp H p f).symm
      rw [w] at c
      exact b.trans c.symm) = compatibleRefinementTransport H p q f w.symm a b := by
  subst q
  apply CompatibleIso.ext_curve
  change b.curve ≪≫ (((baseChangeFunctor f).mapIso a.curve) ≪≫
      (E.baseChangeCompIso p f).symm).symm =
    b.curve ≪≫ (E.baseChangeCompIso p f ≪≫ ((baseChangeFunctor f).mapIso a.curve).symm)
  simp only [Iso.trans_symm, Iso.symm_symm_eq]

/-- A base map proved to be the identity has the actual compatible identity comparison. -/
def compatibleBaseChangeIdEq (g : S ⟶ S) (hg : g = 𝟙 S) :
    CompatibleIso (H.baseChange g) H := by
  subst g
  exact compatibleBaseChangeId H

/-- Transport along a proved identity cancels with the canonical identity comparison. -/
theorem compatibleRefinementTransport_id_eq (f : T ⟶ T) (hf : f = 𝟙 T)
    (w : p = f ≫ p) :
    (compatibleRefinementTransport H p p f w a a).trans
      (compatibleBaseChangeIdEq A f hf) = CompatibleIso.refl A := by
  subst f
  rw [compatibleRefinementTransport_id]
  exact CompatibleIso.symm_trans (compatibleBaseChangeId A)

/-- The cocycle is unchanged when the composite parameter map has its own chosen name. -/
theorem compatibleRefinementTransport_comp_eq {V : Scheme} (r : V ⟶ S)
    (j : V ⟶ U) (k : V ⟶ T) (v : r = j ≫ q) (e : k = j ≫ f) (z : r = k ≫ p)
    {G : GeneralizedEllipticCurve V} {C : G.FiniteSubgroup n}
    (c : CompatibleIso C (H.baseChange r)) :
    (compatibleRefinementTransport H q r j v b c).trans
      ((compatibleRefinementTransport H p q f w.symm a b).baseChange j) =
    (compatibleRefinementTransport H p r k z a c).trans
      (compatibleBaseChangeCompEq A f j k e) := by
  subst k
  exact compatibleRefinementTransport_comp H p q r f j w.symm v a b c

end FLT.Mazur.GeneralizedEllipticCurve.FiniteSubgroup
