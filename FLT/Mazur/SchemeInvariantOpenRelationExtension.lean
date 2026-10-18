/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeInvariantOpenPrincipalExtension
public import FLT.Mazur.SchemeInvariantPrincipalRelationLifts

/-!
# Extending compatible lifts from stable image domains

Relation maps factoring through a stable image open retain their exact
section equations on any specified invariant principal neighborhood.
One common power extends the boundary lift and every relation equation to
the fixed affine target, even when the image open is not affine.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.SchemeFiniteGroupQuotient
open FiniteGroupRestriction
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {G : Type} [Group G] {X Y Z : Scheme}
  (ρ : G →* Aut X) (O : X.Opens) (hO : ∀ g, (ρ g).hom ⁻¹ᵁ O = O)
  (r : invariantCoordinates ρ) (hr : X.basicOpen r.val ≤ O)
  (f g : Z ⟶ X) (hs : f.appTop r.val = g.appTop r.val)
  (fO gO : Z ⟶ O.toScheme) (hf : fO ≫ O.ι = f) (hg : gO ≫ O.ι = g)

include hf hg in
/-- Principal restriction retains a pair equation on its actual open image domain. -/
theorem openPrincipalInvariantMap_pair
    (v : invariantCoordinates (restrictedAction ρ O hO))
    (hv : fO.appTop v.val = gO.appTop v.val) :
    (principalPullbackMap f r.val).appTop
        (openPrincipalInvariantMap ρ O hO r hr v).val =
      (principalPairSecond f g r.val hs).appTop
        (openPrincipalInvariantMap ρ O hO r hr v).val := by
  have h₁ : principalPullbackMap f r.val ≫ X.homOfLE hr =
      (Z.basicOpen (f.appTop r.val)).ι ≫ fO := by
    apply (cancel_mono O.ι).mp
    simp only [Category.assoc, Scheme.homOfLE_ι, principalPullbackMap_inclusion, hf]
  have h₂ : principalPairSecond f g r.val hs ≫ X.homOfLE hr =
      (Z.basicOpen (f.appTop r.val)).ι ≫ gO := by
    apply (cancel_mono O.ι).mp
    simp only [Category.assoc, Scheme.homOfLE_ι, principalPairSecond_inclusion, hg]
  change (principalPullbackMap f r.val ≫ X.homOfLE hr).appTop v.val =
    (principalPairSecond f g r.val hs ≫ X.homOfLE hr).appTop v.val
  rw [h₁, h₂, Scheme.Hom.comp_appTop, Scheme.Hom.comp_appTop]
  exact congrArg (fun t ↦ (Z.basicOpen (f.appTop r.val)).ι.appTop t) hv

variable [Finite G] [IsAffine X] [IsAffine Y] (i : Y ⟶ X)
  {ι : Type} [Finite ι] {T : ι → Scheme} [∀ a, IsAffine (T a)]
  (F H : ∀ a, T a ⟶ X) (hs' : ∀ a, (F a).appTop r.val = (H a).appTop r.val)
  (FO HO : ∀ a, T a ⟶ O.toScheme)
  (hF : ∀ a, FO a ≫ O.ι = F a) (hH : ∀ a, HO a ≫ O.ι = H a)

include hs' hF hH in
/-- An open-domain lift extends with its full boundary and all finite relation equations. -/
theorem open_principal_relation_lift_numerator
    (v : invariantCoordinates (restrictedAction ρ O hO)) (t : Γ(Y, ⊤))
    (hb : (i ∣_ O).appTop v.val = (i ⁻¹ᵁ O).ι.appTop t)
    (he : ∀ a, (FO a).appTop v.val = (HO a).appTop v.val) :
    ∃ (n : ℕ) (w : invariantCoordinates ρ),
      i.appTop w.val = (i.appTop r.val) ^ n * t ∧
      (∀ a, (F a).appTop w.val = (H a).appTop w.val) ∧
      (X.basicOpen r.val).ι.appTop w.val =
        ((X.basicOpen r.val).ι.appTop r.val) ^ n * (X.homOfLE hr).appTop v.val := by
  apply principal_invariant_relation_lift_numerator i ρ r F H hs'
    (openPrincipalInvariantMap ρ O hO r hr v) t
  · rw [openPrincipalInvariantMap_val]
    change (principalPullbackMap i r.val ≫ X.homOfLE hr).appTop v.val = _
    rw [openPrincipalBoundary_square, Scheme.Hom.comp_appTop, CommRingCat.comp_apply, hb]
    change (Y.homOfLE (openPrincipalBoundary_le ρ O r hr i) ≫ (i ⁻¹ᵁ O).ι).appTop t = _
    rw [Scheme.homOfLE_ι]
  · exact fun a ↦ openPrincipalInvariantMap_pair ρ O hO r hr
      (F a) (H a) (hs' a) (FO a) (HO a) (hF a) (hH a) v (he a)

include hr hs' hF hH in
/-- Independent lifts have exact boundary-zero corrections after the same original scalar power. -/
theorem open_principal_relation_correction
    (v : invariantCoordinates (restrictedAction ρ O hO)) (u : invariantCoordinates ρ)
    (hb : (i ∣_ O).appTop v.val = (i ⁻¹ᵁ O).ι.appTop (i.appTop u.val))
    (he : ∀ a, (FO a).appTop v.val = (HO a).appTop v.val) :
    ∃ (n : ℕ) (w : invariantCoordinates ρ), i.appTop w.val = 0 ∧
      ∀ a, (F a).appTop w.val - (H a).appTop w.val =
        (F a).appTop r.val ^ n * ((F a).appTop u.val - (H a).appTop u.val) := by
  obtain ⟨n, w, hw, hf, _⟩ := open_principal_relation_lift_numerator
    ρ O hO r hr i F H hs' FO HO hF hH v (i.appTop u.val) hb he
  refine ⟨n, r ^ n * u - w, ?_, ?_⟩
  · change i.appTop (r.val ^ n * u.val - w.val) = 0
    simp only [map_sub, map_mul, map_pow, hw, sub_self]
  · intro a
    change (F a).appTop (r.val ^ n * u.val - w.val) -
      (H a).appTop (r.val ^ n * u.val - w.val) = _
    simp only [map_sub, map_mul, map_pow, ← hs' a, hf a]
    ring

end FLT.Mazur.SchemeFiniteGroupQuotient
