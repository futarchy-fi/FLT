/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ModuleSheafBinarySections
public import FLT.Mazur.ModuleGlobalSectionPullback

/-!
# Local coefficients of transported global module sections

A semilinear sheaf map that preserves a global section transports a local
multiple of that section by the original scheme section map. The target
open only needs to map into the source open.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules

namespace FLT.Mazur.ModuleSectionTransportRestriction

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u
variable {X Y : Scheme.{u}} (f : X ⟶ Y) {M : Y.Modules} {N : X.Modules}
variable (a : M ⟶ (pushforward f).obj N)

/-- Restriction of the transported global section is transport of its restriction. -/
theorem restrict_global (U : Y.Opens) (s : Γ(M, ⊤)) :
    N.presheaf.map (homOfLE (show f ⁻¹ᵁ U ≤ ⊤ from le_top)).op (a.app ⊤ s) =
      a.app U (M.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op s) := by
  exact (congrArg (fun k ↦ k s)
    (a.mapPresheaf.naturality (homOfLE (show U ≤ ⊤ from le_top)).op)).symm

/-- Local scalar multiplication uses the original morphism on structure-sheaf sections. -/
theorem app_smul (U : Y.Opens) (r : Γ(Y, U)) (s : Γ(M, U)) :
    a.app U (r • s) =
      @SMul.smul Γ(X, f ⁻¹ᵁ U) Γ(N, f ⁻¹ᵁ U) _ (f.app U r) (a.app U s) :=
  a.app_smul r s

/-- A preserved global generator transports each actual local coefficient by pullback. -/
theorem local_coefficient (c s : Γ(M, ⊤)) (d : Γ(N, ⊤))
    (hc : a.app ⊤ c = d) (U : Y.Opens) (V : X.Opens) (h : V ≤ f ⁻¹ᵁ U)
    (r : Γ(Y, U))
    (hs : M.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op s =
      r • M.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op c) :
    N.presheaf.map (homOfLE (show V ≤ ⊤ from le_top)).op (a.app ⊤ s) =
      f.appLE U V h r • N.presheaf.map (homOfLE (show V ≤ ⊤ from le_top)).op d := by
  have ht := restrict_global f a U s
  rw [hs, app_smul, ← restrict_global, hc] at ht
  have hh := congrArg (N.presheaf.map (homOfLE h).op) ht
  have hh' := hh.trans (Scheme.Modules.map_smul N (homOfLE h) (f.app U r)
    (N.presheaf.map (homOfLE (show f ⁻¹ᵁ U ≤ ⊤ from le_top)).op d))
  have hi : (homOfLE (show f ⁻¹ᵁ U ≤ ⊤ from le_top)).op ≫ (homOfLE h).op =
      (homOfLE (show V ≤ ⊤ from le_top)).op := Subsingleton.elim _ _
  simpa only [← ConcreteCategory.comp_apply, ← Functor.map_comp, hi, Scheme.Hom.appLE] using hh'

end FLT.Mazur.ModuleSectionTransportRestriction
