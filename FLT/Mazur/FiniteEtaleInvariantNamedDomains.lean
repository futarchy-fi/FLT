/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteEtaleInvariantOpenTransition

/-!
# Closed invariant transitions on separately named source domains

Transport the exact inverse-image construction to an equal named open. This
keeps the source coefficient ring fixed when a tower uses canonical domains,
instead of a new inverse-image presentation for every transition.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.FiniteEtaleInvariantNamedDomains
open SchemeEffectiveEpiSections
set_option backward.isDefEq.respectTransparency false
variable {D A D' A' : Scheme.{0}} (p q : D ⟶ A) (p' q' : D' ⟶ A')
  (a : A' ⟶ A) (b : D' ⟶ D) (H : IsPullback b p' p a) (hq : b ≫ q = q' ≫ a)
  (U : A.Opens) (V : A'.Opens) (hU : p ⁻¹ᵁ U = q ⁻¹ᵁ U)
  (hV : p' ⁻¹ᵁ V = q' ⁻¹ᵁ V) (hUV : V = a ⁻¹ᵁ U)

/-- Full invariant pullback whose lower ring is the chosen named source domain. -/
def restriction :
    compatibleFunctions (p.resLE U _ le_rfl) (q.resLE U _ hU.le) →+*
      compatibleFunctions (p'.resLE V _ le_rfl) (q'.resLE V _ hV.le) := by
  subst V
  exact FiniteEtaleInvariantOpenTransition.restriction p q p' q' a b H hq U hU

/-- Transport keeps literal source-function restriction, with no coefficient quotient. -/
theorem restriction_val (s : compatibleFunctions (p.resLE U _ le_rfl) (q.resLE U _ hU.le)) :
    (restriction p q p' q' a b H hq U V hU hV hUV s).val =
      (a.resLE U V hUV.le).appTop s.val := by
  subst V
  change (a ∣_ U).appTop s.val = _
  rw [Scheme.Hom.resLE_eq_morphismRestrict a]

variable {S : Scheme.{0}} [IsAffine S] [IsFinite p] [Etale p]
  (f : A ⟶ S) (hf : p ≫ f = q ≫ f) [IsSeparated f]
  (e : CategoryTheory.EquivalenceRelation p q) [IsClosedImmersion a]

include hf e in
/-- Every lower invariant lifts while keeping the actual named domain coefficient rings. -/
theorem restriction_surjective (ha : IsAffineOpen U) :
    Function.Surjective (restriction p q p' q' a b H hq U V hU hV hUV) := by
  subst V
  exact FiniteEtaleInvariantOpenTransition.restriction_surjective
    p q p' q' a b H hq U hU f hf e ha

end FLT.Mazur.FiniteEtaleInvariantNamedDomains
