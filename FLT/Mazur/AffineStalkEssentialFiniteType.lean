/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineClosedPointAlgebra
public import Mathlib.RingTheory.RingHom.EssFiniteType

/-!
# Essential finite type for actual affine stalk coefficients

Localization of affine sections at the specified point gives essential
finite type of the original coefficient map into the actual scheme stalk.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.AffineClosedPointQuotient

set_option backward.isDefEq.respectTransparency false

variable {R : Type*} [CommRing R] {X : Scheme}
  (U : X.affineOpens) (x : U.1) (s : R →+* Γ(X, U))

/-- An actual affine germ is a localization map, hence essentially of finite type. -/
theorem germ_essFiniteType : (X.presheaf.germ U x x.2).hom.EssFiniteType := by
  let _ := TopCat.Presheaf.algebra_section_stalk X.presheaf x
  let _ := U.2.isLocalization_stalk x
  change (algebraMap Γ(X, U) (X.presheaf.stalk x)).EssFiniteType
  rw [RingHom.essFiniteType_algebraMap]
  exact Algebra.EssFiniteType.of_isLocalization _ (U.2.primeIdealOf x).asIdeal.primeCompl

/-- Original finite-type coefficients remain essentially finite type in the actual stalk. -/
theorem stalkScalars_essFiniteType (hs : s.FiniteType) :
    (stalkScalars U x s).EssFiniteType :=
  hs.essFiniteType.comp (germ_essFiniteType U x)

end FLT.Mazur.AffineClosedPointQuotient
