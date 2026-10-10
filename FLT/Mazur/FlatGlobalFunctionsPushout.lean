/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat

/-!
# Flat base change of the actual ring of global functions

For a quasi-compact quasi-separated source and affine bases, a flat cartesian
square induces a pushout square on global functions. In particular a scalar
isomorphism remains an isomorphism after any flat affine base change.
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry

namespace FLT.Mazur.Approximation

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-- Flat affine base change gives a pushout of the original global-section ring maps. -/
theorem isPushout_appTop_of_flat_cartesian {P X T S : Scheme.{u}}
    [CompactSpace X] [QuasiSeparatedSpace X] [IsAffine S] [IsAffine T]
    {a : P ⟶ X} {q : P ⟶ T} {f : X ⟶ S} {g : T ⟶ S} [Flat g]
    (h : IsPullback a q f g) : IsPushout f.appTop g.appTop a.appTop q.appTop := by
  have htop : (⊤ : P.Opens) = a ⁻¹ᵁ ⊤ ⊓ q ⁻¹ᵁ ⊤ := by simp
  have hi := isIso_pushoutSection_of_isQuasiSeparated_of_flat_right h
    (US := ⊤) (UT := ⊤) (UX := ⊤) (by simp) (by simp) htop
    (isAffineOpen_top S) (isAffineOpen_top T) isCompact_univ isQuasiSeparated_univ
  simpa [Scheme.Hom.appLE, Scheme.Hom.appTop] using
    (isIso_pushoutSection_iff h (by simp) (by simp) htop).mp hi

/-- An actual scalar isomorphism persists under flat affine base change. -/
theorem isIso_appTop_of_flat_cartesian {P X T S : Scheme.{u}}
    [CompactSpace X] [QuasiSeparatedSpace X] [IsAffine S] [IsAffine T]
    {a : P ⟶ X} {q : P ⟶ T} {f : X ⟶ S} {g : T ⟶ S} [Flat g]
    (h : IsPullback a q f g) [IsIso f.appTop] : IsIso q.appTop :=
  (isPushout_appTop_of_flat_cartesian h).isIso_inr_of_isIso

end FLT.Mazur.Approximation
