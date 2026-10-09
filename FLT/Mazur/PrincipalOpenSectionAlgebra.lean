/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.AlgebraicGeometry.AffineScheme

/-!
# Localization scalars from a geometric principal-open factorization

Factoring through a principal open makes its defining function invertible on
actual global sections. The universal localization lift supplies a compatible
algebra action, rather than asking for one as additional geometric data.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.PrincipalOpenSectionAlgebra

variable {T S : Scheme.{0}} (g : T ⟶ S) (r : Γ(S, ⊤))

/-- Pullback through the actual principal open inverts its defining function. -/
lemma isUnit_of_factor [IsAffine S] (t : T ⟶ (S.basicOpen r).toScheme)
    (ht : t ≫ (S.basicOpen r).ι = g) : IsUnit (g.appTop r) := by
  subst g
  have hr : IsUnit (algebraMap Γ(S, ⊤) Γ(S.basicOpen r, ⊤) r) :=
    IsLocalization.Away.algebraMap_isUnit r
  exact hr.map t.appTop.hom

/-- The localization-ring map induced by an invertible pulled-back section. -/
def sectionLift (hr : IsUnit (g.appTop r)) : Localization.Away r →+* Γ(T, ⊤) :=
  IsLocalization.Away.lift r hr

/-- On original scalars the lift is the actual structural pullback. -/
lemma sectionLift_algebraMap (hr : IsUnit (g.appTop r)) (a : Γ(S, ⊤)) :
    sectionLift g r hr (algebraMap Γ(S, ⊤) (Localization.Away r) a) = g.appTop a :=
  IsLocalization.Away.lift_eq r hr a

/-- Localized scalars act on actual global functions. -/
@[instance_reducible] def sectionAlgebra (hr : IsUnit (g.appTop r)) :
    Algebra (Localization.Away r) Γ(T, ⊤) :=
  (sectionLift g r hr).toAlgebra

/-- The localized action extends the original structural action. -/
lemma sectionAlgebra_tower (hr : IsUnit (g.appTop r)) :
    let _ : Algebra Γ(S, ⊤) Γ(T, ⊤) := g.appTop.hom.toAlgebra
    let _ := sectionAlgebra g r hr
    IsScalarTower Γ(S, ⊤) (Localization.Away r) Γ(T, ⊤) := by
  dsimp only
  let _ : Algebra Γ(S, ⊤) Γ(T, ⊤) := g.appTop.hom.toAlgebra
  let _ := sectionAlgebra g r hr
  exact IsScalarTower.of_algebraMap_eq fun a ↦ (sectionLift_algebraMap g r hr a).symm

/-- An actual factorization supplies both the localization action and its compatibility. -/
theorem exists_sectionAlgebra_of_factor [IsAffine S] (t : T ⟶ (S.basicOpen r).toScheme)
    (ht : t ≫ (S.basicOpen r).ι = g) :
    let _ : Algebra Γ(S, ⊤) Γ(T, ⊤) := g.appTop.hom.toAlgebra
    ∃ a : Algebra (Localization.Away r) Γ(T, ⊤),
      let _ := a
      IsScalarTower Γ(S, ⊤) (Localization.Away r) Γ(T, ⊤) :=
  ⟨sectionAlgebra g r (isUnit_of_factor g r t ht),
    sectionAlgebra_tower g r (isUnit_of_factor g r t ht)⟩

end FLT.Mazur.PrincipalOpenSectionAlgebra
