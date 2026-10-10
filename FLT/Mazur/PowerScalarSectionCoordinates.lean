/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.IdealPowerReesSingle
public import FLT.Mazur.PowerCohomologyScalarMaps

/-!
# Homogeneous scalar lifts in original section coordinates

The scalar map on original ideal-power sheaves agrees with polynomial
multiplication under their original affine Rees coordinates.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry
open Scheme.Modules FLT.Mazur.GlobalIdealPower FLT.Mazur.IdealPowerScalarLift
open scoped DirectSum

universe u

namespace FLT.Mazur.IdealAdicQuotient

variable {X : Scheme.{u}} [IsLocallyNoetherian X]
  {R : Type u} [CommRing R] (ρ : R →+* Γ(X, ⊤))
  (I : X.IdealSheafData) (M : X.Modules) [M.IsFinitePresentation]
  (J : Ideal R)
  (hJ : ∀ r : R, r ∈ J → ∀ U : X.affineOpens,
    X.presheaf.map U.1.leTop.op (ρ r) ∈ I.ideal U)

/-- The original lifted map retains scalar multiplication after the original inclusion. -/
lemma powerScalarMap_app_inclusion (a n : ℕ) (r : ↥(J ^ a)) (U : X.Opens)
    (s : Γ(power I n M, U)) :
    (inclusion (I ^ (a + n)) M).app U ((powerScalarMap ρ I M J hJ a n r).app U s) =
      X.presheaf.map U.leTop.op (ρ r) • (inclusion (I ^ n) M).app U s := by
  have h := ConcreteCategory.congr_hom
    (congrArg (fun g ↦ g.app U) (powerScalarMap_inclusion ρ I M J hJ a n r)) s
  exact h.trans ((inclusion (I ^ n) M).app_smul _ _)

/-- Homogeneous polynomial multiplication is the original lifted power-sheaf map. -/
lemma powerScalarMap_sections (a n : ℕ) (r : ↥(J ^ a)) (V : X.affineOpens)
    (s : Γ(power I n M, V.1)) :
    let _ := IdealPowerRees.sectionsModule I M V
    (⟨Polynomial.monomial a (X.presheaf.map V.1.leTop.op (ρ r)),
      reesAlgebra.monomial_mem.mpr (by
        simpa using basePowerScalar_mem ρ I J hJ a r r.property V)⟩ :
        reesAlgebra (I.ideal V)) • DirectSum.of (fun k ↦ Γ(power I k M, V.1)) n s =
      DirectSum.of (fun k ↦ Γ(power I k M, V.1)) (a + n)
        ((powerScalarMap ρ I M J hJ a n r).app V.1 s) := by
  let _ := IdealPowerRees.sectionsModule I M V
  apply (IdealPowerRees.sectionsEquiv I M V).injective
  apply Subtype.ext
  rw [IdealPowerRees.sectionsEquiv_monomial_smul_of I M V a n
    ⟨_, by simpa using basePowerScalar_mem ρ I J hJ a r r.property V⟩,
    IdealPowerRees.sectionsEquiv_of, powerScalarMap_app_inclusion]

end FLT.Mazur.IdealAdicQuotient
