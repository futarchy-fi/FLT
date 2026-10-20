/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteEtaleInvariantNamedDomains

/-!
# Direct function formulas on named invariant domains

Construct the named-domain map directly from source-function pullback. Its
comparison with the exact inverse-image presentation is proved generically,
so consumers need not reduce equality transport on large rank-stage schemes.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.FiniteEtaleInvariantDomainCoefficients
open SchemeEffectiveEpiSections
set_option backward.isDefEq.respectTransparency false
variable {D A D' A' : Scheme.{0}} (p q : D ⟶ A) (p' q' : D' ⟶ A')
  (a : A' ⟶ A) (b : D' ⟶ D) (H : IsPullback b p' p a) (hq : b ≫ q = q' ≫ a)
  (U : A.Opens) (V : A'.Opens) (hU : p ⁻¹ᵁ U = q ⁻¹ᵁ U)
  (hV : p' ⁻¹ᵁ V = q' ⁻¹ᵁ V) (hUV : V = a ⁻¹ᵁ U)

include H hq in
/-- Direct source pullback preserves the complete independent-endpoint equation. -/
theorem pullback_mem (s : compatibleFunctions (p.resLE U _ le_rfl) (q.resLE U _ hU.le)) :
    (a.resLE U V hUV.le).appTop s.val ∈
      compatibleFunctions (p'.resLE V _ le_rfl) (q'.resLE V _ hV.le) := by
  have hb : p' ⁻¹ᵁ V ≤ b ⁻¹ᵁ (p ⁻¹ᵁ U) := by
    rw [hUV, ← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, H.w]
  let v := b.resLE _ _ hb
  have hp : v ≫ p.resLE U _ le_rfl = p'.resLE V _ le_rfl ≫ a.resLE U V hUV.le := by
    apply (cancel_mono U.ι).mp
    simp only [Category.assoc, Scheme.Hom.resLE_comp_ι,
      Scheme.Hom.resLE_comp_ι_assoc, v, H.w]
  have hs : v ≫ q.resLE U _ hU.le = q'.resLE V _ hV.le ≫ a.resLE U V hUV.le := by
    apply (cancel_mono U.ι).mp
    simp only [Category.assoc, Scheme.Hom.resLE_comp_ι,
      Scheme.Hom.resLE_comp_ι_assoc, v, hq]
  have he := congrArg v.appTop s.property
  change (v ≫ p.resLE U _ le_rfl).appTop s.val =
    (v ≫ q.resLE U _ hU.le).appTop s.val at he
  change (p'.resLE V _ le_rfl ≫ a.resLE U V hUV.le).appTop s.val =
    (q'.resLE V _ hV.le ≫ a.resLE U V hUV.le).appTop s.val
  rwa [hp, hs] at he

/-- Full invariant coefficient pullback with a definitionally literal function formula. -/
def restriction :
    compatibleFunctions (p.resLE U _ le_rfl) (q.resLE U _ hU.le) →+*
      compatibleFunctions (p'.resLE V _ le_rfl) (q'.resLE V _ hV.le) :=
  ((a.resLE U V hUV.le).appTop.hom.comp (compatibleFunctions _ _).subtype).codRestrict _
    (pullback_mem p q p' q' a b H hq U V hU hV hUV)

/-- No scheme equality transport is needed to compute the underlying coefficient. -/
theorem restriction_val (s : compatibleFunctions (p.resLE U _ le_rfl) (q.resLE U _ hU.le)) :
    (restriction p q p' q' a b H hq U V hU hV hUV s).val =
      (a.resLE U V hUV.le).appTop s.val := rfl

/-- The direct formula is exactly the established closed-transition map. -/
theorem restriction_eq : restriction p q p' q' a b H hq U V hU hV hUV =
    FiniteEtaleInvariantNamedDomains.restriction p q p' q' a b H hq U V hU hV hUV := by
  ext s
  exact (FiniteEtaleInvariantNamedDomains.restriction_val
    p q p' q' a b H hq U V hU hV hUV s).symm

variable {S : Scheme.{0}} [IsAffine S] [IsFinite p] [Etale p]
  (f : A ⟶ S) (hf : p ≫ f = q ≫ f) [IsSeparated f]
  (e : CategoryTheory.EquivalenceRelation p q) [IsClosedImmersion a]

include hf e in
/-- The direct coefficient map inherits geometric surjectivity on affine domains. -/
theorem restriction_surjective (ha : IsAffineOpen U) :
    Function.Surjective (restriction p q p' q' a b H hq U V hU hV hUV) := by
  rw [restriction_eq]
  exact FiniteEtaleInvariantNamedDomains.restriction_surjective
    p q p' q' a b H hq U V hU hV hUV f hf e ha

end FLT.Mazur.FiniteEtaleInvariantDomainCoefficients
