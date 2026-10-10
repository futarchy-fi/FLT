/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.BaseAdicReesRestriction
public import FLT.Mazur.PrincipalLocalizationSquare

/-!
# Principal coordinates on actual affine opens over a base

A geometric equality with a principal open gives a base-linear equivalence
from the literal localization to its section ring. Its numerator formula
retains the actual structure-sheaf restriction map.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open FLT.Mazur.BaseAdicRees

namespace FLT.Mazur.Approximation

universe u

variable {R : CommRingCat.{u}} {X : Scheme.{u}} (f : X ⟶ Spec R)
  (U W : X.affineOpens) (r : Γ(X, U.1)) (he : W.1 = X.basicOpen r)

/-- The actual section restriction identifies the literal principal localization. -/
def principalAffineOpenEquiv :
    let _ := chartAlgebra f U
    let _ := chartAlgebra f W
    Localization.Away r ≃ₐ[R] Γ(X, W.1) := by
  let _ := chartAlgebra f U
  let _ := chartAlgebra f W
  let h : W.1 ≤ U.1 := he ▸ X.basicOpen_le r
  let _ : Algebra Γ(X, U.1) Γ(X, W.1) :=
    (X.presheaf.map (homOfLE h).op).hom.toAlgebra
  let _ : IsScalarTower R Γ(X, U.1) Γ(X, W.1) :=
    IsScalarTower.of_algebraMap_eq fun c ↦ ((chartRingRestriction f h).commutes c).symm
  let _ := U.2.isLocalization_of_eq_basicOpen r (homOfLE h) he
  exact (IsLocalization.algEquiv (Submonoid.powers r)
    (Localization.Away r) Γ(X, W.1)).restrictScalars R

/-- On numerators the equivalence is exactly restriction of original sections. -/
theorem principalAffineOpenEquiv_numerator (s : Γ(X, U.1)) :
    principalAffineOpenEquiv f U W r he (algebraMap Γ(X, U.1) (Localization.Away r) s) =
      X.presheaf.map (homOfLE (he ▸ X.basicOpen_le r)).op s := by
  let h : W.1 ≤ U.1 := he ▸ X.basicOpen_le r
  let _ : Algebra Γ(X, U.1) Γ(X, W.1) :=
    (X.presheaf.map (homOfLE h).op).hom.toAlgebra
  let _ := U.2.isLocalization_of_eq_basicOpen r (homOfLE h) he
  exact (IsLocalization.algEquiv (Submonoid.powers r)
    (Localization.Away r) Γ(X, W.1)).commutes s

/-- Localizing at one gives a uniform principal target for every shared overlap. -/
def affineOpenUnitEquiv :
    let _ := chartAlgebra f W
    Γ(X, W.1) ≃ₐ[R] Localization.Away (1 : Γ(X, W.1)) := by
  let _ := chartAlgebra f W
  exact (IsLocalization.atOne _ _ : Γ(X, W.1) ≃ₐ[Γ(X, W.1)]
    Localization.Away (1 : Γ(X, W.1))).restrictScalars R

/-- The unit-localization equivalence is the canonical localization map. -/
theorem affineOpenUnitEquiv_apply (s : Γ(X, W.1)) :
    affineOpenUnitEquiv f W s =
      algebraMap Γ(X, W.1) (Localization.Away (1 : Γ(X, W.1))) s := by
  exact (IsLocalization.atOne _ _ : Γ(X, W.1) ≃ₐ[Γ(X, W.1)]
    Localization.Away (1 : Γ(X, W.1))).commutes s

end FLT.Mazur.Approximation
