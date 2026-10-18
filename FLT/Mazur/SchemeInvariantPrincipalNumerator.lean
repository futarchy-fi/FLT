/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeFiniteGroupPrincipalQuotient

/-!
# Invariant numerators on actual principal scheme charts

An invariant function on an invariant principal open of an affine scheme has
an invariant numerator on the original scheme. The denominator is a power of
the specified original function, even in positive characteristic and in the
presence of zero divisors.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open FLT.Mazur.SchemeCoordinateAction
namespace FLT.Mazur.SchemeFiniteGroupQuotient
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {G : Type} [Group G] [Finite G] {X : Scheme} [IsAffine X]
  (ρ : G →* Aut X) (r : invariantCoordinates ρ)

/-- The principal restriction has a numerator invariant under the original action. -/
theorem principal_invariant_numerator
    (v : invariantCoordinates (principalAction ρ r)) :
    ∃ (n : ℕ) (w : invariantCoordinates ρ),
      (X.basicOpen r.val).ι.appTop w.val =
        ((X.basicOpen r.val).ι.appTop r.val) ^ n * v.val := by
  let _ := coordinateAction ρ
  let _ := coordinateAction (principalAction ρ r)
  let U := X.basicOpen r.val
  have he (g : G) (a : Γ(X, ⊤)) :
      g • algebraMap Γ(X, ⊤) Γ(U, ⊤) a = algebraMap Γ(X, ⊤) Γ(U, ⊤) (g • a) := by
    exact congrArg (fun k : Γ(X, ⊤) →+* Γ(U, ⊤) ↦ k a)
      (coordinateHom_comp (principalAction ρ r) ρ U.ι (principal_ι_equivariant ρ r) g)
  obtain ⟨n, w, hw⟩ := FiniteGroupQuotient.exists_invariant_numerator
    G Γ(X, ⊤) r Γ(U, ⊤) he v.val v.property
  exact ⟨n, w, (mul_comm _ _).trans hw |>.symm⟩

omit [Finite G] in
/-- Equality after principal restriction is killed by an original scalar power. -/
theorem principal_sections_eq_power (a b : Γ(X, ⊤))
    (h : (X.basicOpen r.val).ι.appTop a = (X.basicOpen r.val).ι.appTop b) :
    ∃ n : ℕ, r.val ^ n * a = r.val ^ n * b :=
  IsLocalization.Away.exists_of_eq r.val h

end FLT.Mazur.SchemeFiniteGroupQuotient
