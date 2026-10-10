/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.AlgebraicGeometry.Restrict

/-!
# Ambient sections and top sections under restriction

The canonical top-section comparison commutes with inclusions of opens and
with restricted scheme morphisms. Both directions are exposed for unit descent.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.Approximation

universe u

variable {X Y : Scheme.{u}}

/-- Passing from ambient to top sections commutes with restriction. -/
theorem topIso_inv_restriction {U V : X.Opens} (h : U ≤ V) (x : Γ(X, V)) :
    (X.homOfLE h).appTop (V.topIso.inv x) =
      U.topIso.inv (X.presheaf.map (homOfLE h).op x) := by
  exact (congrArg (fun k ↦ k x) (X.restrictFunctorΓ.inv.naturality (homOfLE h).op)).symm

/-- Passing from top to ambient sections commutes with restriction. -/
theorem topIso_hom_restriction {U V : X.Opens} (h : U ≤ V)
    (x : Γ(V.toScheme, ⊤)) :
    X.presheaf.map (homOfLE h).op (V.topIso.hom x) =
      U.topIso.hom ((X.homOfLE h).appTop x) := by
  exact (congrArg (fun k ↦ k x) (X.restrictFunctorΓ.hom.naturality (homOfLE h).op)).symm

/-- Top sections of a restricted morphism recover the ambient section pullback. -/
theorem topIso_hom_resLE (f : X ⟶ Y) (U : Y.Opens) (V : X.Opens)
    (h : V ≤ f ⁻¹ᵁ U) (x : Γ(U.toScheme, ⊤)) :
    f.appLE U V h (U.topIso.hom x) = V.topIso.hom ((f.resLE U V h).appTop x) := by
  rw [Scheme.Hom.appTop, Scheme.Hom.resLE_app_top]
  simp only [CommRingCat.comp_apply, Iso.inv_hom_id_apply]

end FLT.Mazur.Approximation
