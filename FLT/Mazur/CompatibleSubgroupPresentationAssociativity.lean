/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CompatibleSubgroupPresentationExtension

/-!
# Associativity of compatible subgroup presentations

Flattening three successive subgroup presentations is independent of the
parenthesization, with the actual associativity equality on parameter maps.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.GeneralizedEllipticCurve.FiniteSubgroup
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {S T U V : Scheme} {n : ℕ} {E : GeneralizedEllipticCurve S}

/-- Inverting a full compatible comparison twice restores that comparison. -/
@[simp] theorem CompatibleIso.symm_symm_eq {F : GeneralizedEllipticCurve S}
    {H : E.FiniteSubgroup n} {J : F.FiniteSubgroup n} (a : CompatibleIso H J) :
    a.symm.symm = a := by
  apply CompatibleIso.ext_curve
  exact Iso.symm_symm_eq a.curve

/-- Inversion reverses composition of full compatible comparisons. -/
theorem CompatibleIso.trans_symm_eq {F G : GeneralizedEllipticCurve S}
    {H : E.FiniteSubgroup n} {J : F.FiniteSubgroup n} {K : G.FiniteSubgroup n}
    (a : CompatibleIso H J) (b : CompatibleIso J K) :
    (a.trans b).symm = b.symm.trans a.symm := by
  apply CompatibleIso.ext_curve
  exact Iso.trans_symm a.curve b.curve

/-- Rewriting the source of an inverse pullback comparison retains its actual inverse. -/
theorem compatibleBaseChangeCompEq_inv_cast (H : E.FiniteSubgroup n)
    (p : T ⟶ S) (q : U ⟶ T) (f : U ⟶ S) (w : f = q ≫ p)
    {F : GeneralizedEllipticCurve U} {B : F.FiniteSubgroup n}
    (a : CompatibleIso B ((H.baseChange p).baseChange q)) :
    (by
      have d := a.trans (compatibleBaseChangeCompEq H p q f w).symm
      rw [w] at d
      exact d) = a.trans (compatibleBaseChangeComp H p q).symm := by
  subst f
  rfl

/-- Renaming the original parameter projection preserves the full presentation transport. -/
theorem compatibleRefinementTransport_source_cast (H : E.FiniteSubgroup n)
    (p : T ⟶ S) (q r : U ⟶ S) (f : U ⟶ T) (w : q = f ≫ p) (e : r = q)
    {D : GeneralizedEllipticCurve T} {F : GeneralizedEllipticCurve U}
    {A : D.FiniteSubgroup n} {B : F.FiniteSubgroup n}
    (a : CompatibleIso A (H.baseChange p)) (b : CompatibleIso B (H.baseChange q)) :
    compatibleRefinementTransport H p r f (e.trans w) a
        (by rw [e]; exact b) = compatibleRefinementTransport H p q f w a b := by
  subst r
  rfl

/-- Either order of extending three presentations gives the same actual compatible map. -/
theorem compatiblePresentationExtension_assoc (H : E.FiniteSubgroup n)
    (p : T ⟶ S) (q : U ⟶ T) (r : V ⟶ U)
    {D : GeneralizedEllipticCurve T} {F : GeneralizedEllipticCurve U}
    {G : GeneralizedEllipticCurve V}
    {A : D.FiniteSubgroup n} {B : F.FiniteSubgroup n} {C : G.FiniteSubgroup n}
    (a : CompatibleIso A (H.baseChange p)) (b : CompatibleIso B (A.baseChange q))
    (c : CompatibleIso C (B.baseChange r)) :
    compatiblePresentationExtension H (q ≫ p)
        (compatiblePresentationExtension H p a q b) r c =
      (by
        have d := compatiblePresentationExtension H p a (r ≫ q)
          (compatiblePresentationExtension A q b r c)
        rw [Category.assoc] at d
        exact d) := by
  have hc := compatibleBaseChangeExtension_comp H p a.symm q r
  have hi := congrArg CompatibleIso.symm hc
  simp only [CompatibleIso.trans_symm_eq, CompatibleIso.baseChange_symm,
    CompatibleIso.symm_symm_eq, CompatibleIso.baseChange_trans] at hi
  have hh := congrArg (fun z ↦ c.trans ((b.baseChange r).trans z)) hi
  have he : compatiblePresentationExtension H p a (r ≫ q)
      (compatiblePresentationExtension A q b r c) =
      (c.trans ((compatiblePresentationExtension H p a q b).baseChange r)).trans
        (compatibleBaseChangeCompEq H (q ≫ p) r ((r ≫ q) ≫ p)
          (Category.assoc r q p)).symm := by
    simpa only [compatiblePresentationExtension, CompatibleIso.baseChange_trans,
      CompatibleIso.baseChange_symm, CompatibleIso.trans_assoc] using hh
  simp only [he]
  exact (compatibleBaseChangeCompEq_inv_cast H (q ≫ p) r ((r ≫ q) ≫ p)
    (Category.assoc r q p)
    (c.trans ((compatiblePresentationExtension H p a q b).baseChange r))).symm

end FLT.Mazur.GeneralizedEllipticCurve.FiniteSubgroup
