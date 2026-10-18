/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeInvariantOpenRelationExtension

/-!
# Restricting relation equations from a common open domain

An equation on the part of a relation whose two endpoints lie in the usable
open restricts to an original principal neighborhood. Neither full endpoint
map is required to factor through the usable open. The omitted relation
points are handled later by clearing powers on the original affine relation.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.SchemeFiniteGroupQuotient
open FiniteGroupRestriction
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {G : Type} [Group G] {X Z : Scheme}
  (ρ : G →* Aut X) (O : X.Opens) (hO : ∀ g, (ρ g).hom ⁻¹ᵁ O = O)
  (r : invariantCoordinates ρ) (hr : X.basicOpen r.val ≤ O)
  (f g : Z ⟶ X) (hs : f.appTop r.val = g.appTop r.val)

/-- The full relation domain on which both endpoints lie in the usable open. -/
def pairOpenDomain : Z.Opens := f ⁻¹ᵁ O ⊓ g ⁻¹ᵁ O

/-- The first actual endpoint on the common open relation domain. -/
def pairOpenFirst : (pairOpenDomain O f g).toScheme ⟶ O.toScheme :=
  f.resLE O _ inf_le_left

/-- The second actual endpoint on the common open relation domain. -/
def pairOpenSecond : (pairOpenDomain O f g).toScheme ⟶ O.toScheme :=
  g.resLE O _ inf_le_right

include hr hs in
/-- Equal original scalars put the principal relation inside the common usable domain. -/
theorem principal_le_pairOpenDomain :
    Z.basicOpen (f.appTop r.val) ≤ pairOpenDomain O f g := by
  apply le_inf
  · exact openPrincipalBoundary_le ρ O r hr f
  · rw [hs]
    exact openPrincipalBoundary_le ρ O r hr g

/-- The first principal endpoint factors through the actual open relation domain. -/
theorem principal_pairOpen_first_square :
    principalPullbackMap f r.val ≫ X.homOfLE hr =
      Z.homOfLE (principal_le_pairOpenDomain ρ O r hr f g hs) ≫ pairOpenFirst O f g := by
  apply (cancel_mono O.ι).mp
  simp only [pairOpenFirst, Category.assoc, Scheme.Hom.resLE_comp_ι,
    Scheme.homOfLE_ι, principalPullbackMap_inclusion, Scheme.homOfLE_ι_assoc]

/-- The second principal endpoint factors through the same open relation domain. -/
theorem principal_pairOpen_second_square :
    principalPairSecond f g r.val hs ≫ X.homOfLE hr =
      Z.homOfLE (principal_le_pairOpenDomain ρ O r hr f g hs) ≫ pairOpenSecond O f g := by
  apply (cancel_mono O.ι).mp
  simp only [pairOpenSecond, Category.assoc, Scheme.Hom.resLE_comp_ι,
    Scheme.homOfLE_ι, principalPairSecond_inclusion, Scheme.homOfLE_ι_assoc]

/-- Compatibility on the open relation suffices; the full endpoints need not land in the open. -/
theorem openPrincipalInvariantMap_pairOpen
    (v : invariantCoordinates (restrictedAction ρ O hO))
    (hv : (pairOpenFirst O f g).appTop v.val = (pairOpenSecond O f g).appTop v.val) :
    (principalPullbackMap f r.val).appTop
        (openPrincipalInvariantMap ρ O hO r hr v).val =
      (principalPairSecond f g r.val hs).appTop
        (openPrincipalInvariantMap ρ O hO r hr v).val := by
  change (principalPullbackMap f r.val ≫ X.homOfLE hr).appTop v.val =
    (principalPairSecond f g r.val hs ≫ X.homOfLE hr).appTop v.val
  rw [principal_pairOpen_first_square ρ O r hr f g hs,
    principal_pairOpen_second_square ρ O r hr f g hs,
    Scheme.Hom.comp_appTop, Scheme.Hom.comp_appTop]
  exact congrArg (fun t ↦
    (Z.homOfLE (principal_le_pairOpenDomain ρ O r hr f g hs)).appTop t) hv

end FLT.Mazur.SchemeFiniteGroupQuotient
