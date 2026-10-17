/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteFlatAffineLocalFree

/-!
# Finite-projective global sections of finite flat morphisms

The module structure is the actual global section map. Finiteness, flatness,
and local finite presentation imply projectivity, with no chosen basis.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.FCurve
universe u
variable {D A : Scheme.{u}} [IsAffine A] (p : D ⟶ A)
  [IsFinite p] [Flat p] [LocallyOfFinitePresentation p]

/-- Finite flat finitely presented morphisms have projective original global sections. -/
theorem finiteFlat_appTop_projective :
    let _ := p.appTop.hom.toAlgebra
    Module.Projective Γ(A, ⊤) Γ(D, ⊤) := by
  let _ : IsAffine D := isAffine_of_isAffineHom p
  let _ := p.appTop.hom.toAlgebra
  let _ : Module.Finite Γ(A, ⊤) Γ(D, ⊤) := p.finite_appTop
  let _ : Algebra.FinitePresentation Γ(A, ⊤) Γ(D, ⊤) := p.finitePresentation_appTop
  let _ : Module.FinitePresentation Γ(A, ⊤) Γ(D, ⊤) :=
    Module.FinitePresentation.of_finite_of_finitePresentation _ _
  let _ : Module.Flat Γ(A, ⊤) Γ(D, ⊤) := p.flat_appTop
  exact Module.Flat.projective_of_finitePresentation

end FLT.Mazur.FCurve
