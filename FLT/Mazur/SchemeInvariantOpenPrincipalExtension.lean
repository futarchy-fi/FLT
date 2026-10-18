/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeInvariantPrincipalBoundaryNumerator

/-!
# Extending invariant boundary lifts from arbitrary stable open domains

A section may be defined on a nonaffine stable image open. Any specified
invariant principal open contained in that domain lets us extend it back to
the fixed affine target after a power of the specified original scalar.
The full boundary equation is retained; existence of that scalar is separate.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.SchemeFiniteGroupQuotient
open FiniteGroupRestriction
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {G : Type} [Group G] {X Y : Scheme}
  (ρ : G →* Aut X) (O : X.Opens) (hO : ∀ g, (ρ g).hom ⁻¹ᵁ O = O)
  (r : invariantCoordinates ρ) (hr : X.basicOpen r.val ≤ O)

/-- Restriction from the stable image domain to a specified original principal neighborhood. -/
def openPrincipalInvariantMap :
    invariantCoordinates (restrictedAction ρ O hO) →+*
      invariantCoordinates (principalAction ρ r) :=
  invariantMap (principalAction ρ r) (restrictedAction ρ O hO) (X.homOfLE hr)
    (fun g ↦ (inclusion_equivariant ρ O hO _ (basicOpen_stable ρ r) hr g).symm)

/-- This invariant map is the actual open restriction on underlying functions. -/
theorem openPrincipalInvariantMap_val (v : invariantCoordinates (restrictedAction ρ O hO)) :
    (openPrincipalInvariantMap ρ O hO r hr v).val = (X.homOfLE hr).appTop v.val := rfl

variable (i : Y ⟶ X)

include hr in
/-- The same principal containment holds on the unchanged inverse-image boundary. -/
theorem openPrincipalBoundary_le : Y.basicOpen (i.appTop r.val) ≤ i ⁻¹ᵁ O := by
  rw [← Scheme.preimage_basicOpen_top]
  exact i.preimage_mono hr

/-- The principal restriction square commutes with the full original boundary map. -/
@[reassoc] theorem openPrincipalBoundary_square :
    principalPullbackMap i r.val ≫ X.homOfLE hr =
      Y.homOfLE (openPrincipalBoundary_le ρ O r hr i) ≫ (i ∣_ O) := by
  apply (cancel_mono O.ι).mp
  simp only [Category.assoc, Scheme.homOfLE_ι, principalPullbackMap_inclusion,
    morphismRestrict_ι, Scheme.homOfLE_ι_assoc]

variable [Finite G] [IsAffine X] [IsAffine Y]

/-- A lift on any stable open extends to the original affine target with an exact boundary. -/
theorem open_principal_boundary_lift_numerator
    (v : invariantCoordinates (restrictedAction ρ O hO)) (t : Γ(Y, ⊤))
    (hv : (i ∣_ O).appTop v.val = (i ⁻¹ᵁ O).ι.appTop t) :
    ∃ (n : ℕ) (w : invariantCoordinates ρ),
      i.appTop w.val = (i.appTop r.val) ^ n * t ∧
      (X.basicOpen r.val).ι.appTop w.val =
        ((X.basicOpen r.val).ι.appTop r.val) ^ n * (X.homOfLE hr).appTop v.val := by
  apply principal_invariant_boundary_lift_numerator i ρ r
    (openPrincipalInvariantMap ρ O hO r hr v) t
  rw [openPrincipalInvariantMap_val]
  change (principalPullbackMap i r.val ≫ X.homOfLE hr).appTop v.val = _
  rw [openPrincipalBoundary_square, Scheme.Hom.comp_appTop, CommRingCat.comp_apply, hv]
  change (Y.homOfLE (openPrincipalBoundary_le ρ O r hr i) ≫ (i ⁻¹ᵁ O).ι).appTop t = _
  rw [Scheme.homOfLE_ι]

/-- Boundary-zero corrections on nonaffine image domains extend without changing the target. -/
theorem open_principal_boundary_kernel_numerator
    (v : invariantCoordinates (restrictedAction ρ O hO)) (hv : (i ∣_ O).appTop v.val = 0) :
    ∃ (n : ℕ) (w : invariantCoordinates ρ), i.appTop w.val = 0 ∧
      (X.basicOpen r.val).ι.appTop w.val =
        ((X.basicOpen r.val).ι.appTop r.val) ^ n * (X.homOfLE hr).appTop v.val := by
  obtain ⟨n, w, hw, he⟩ := open_principal_boundary_lift_numerator ρ O hO r hr i v 0
    (by simpa only [map_zero] using hv)
  exact ⟨n, w, by simpa only [mul_zero] using hw, he⟩

end FLT.Mazur.SchemeFiniteGroupQuotient
