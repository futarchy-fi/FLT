/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.InvariantOpenCoefficientGluing
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated

/-!
# Detecting equality on a named principal open of a qcqs scheme

Equality of full sections on the named open is equivalent to equality after
one global scalar power. This applies to nonaffine sources and retains all
nilpotents; it is not a test on reduced points.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.SchemePrincipalSectionPowerDetection
set_option backward.isDefEq.respectTransparency false
variable {X : Scheme.{0}} [CompactSpace X] [QuasiSeparatedSpace X]

/-- Clear a full-section equality on the actual named principal domain. -/
theorem exists_power_eq (r : Γ(X, ⊤)) (U : X.Opens) (hU : X.basicOpen r = U)
    (s t : Γ(X, ⊤)) (h : U.ι.appTop s = U.ι.appTop t) :
    ∃ N : ℕ, r ^ N * s = r ^ N * t := by
  subst U
  have hh := congrArg (X.basicOpen r).topIso.hom h
  simp only [InvariantOpenCoefficientGluing.inclusion_coordinates] at hh
  let _ : IsLocalization.Away r Γ(X, X.basicOpen r) :=
    isLocalization_basicOpen_of_qcqs isCompact_univ isQuasiSeparated_univ _
  exact IsLocalization.Away.exists_of_eq r hh

end FLT.Mazur.SchemePrincipalSectionPowerDetection
