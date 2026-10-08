/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GlobalIdealPower
public import FLT.Mazur.ReesModuleDirectSum
public import FLT.Mazur.CoherentAffineCoverSections

/-!
# Affine Rees coordinates for the original ideal-power sheaves

The full direct sum of actual power sections identifies with the ordinary
Rees module of the ideal-action filtration. This module is finite over the
local Rees algebra. Its finiteness is not a claim about cohomology over the
base Rees algebra.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry
open Scheme.Modules FLT.Mazur.GlobalIdealPower FLT.Mazur.FCurve
open scoped DirectSum

universe u

namespace FLT.Mazur.IdealPowerRees

variable {X : Scheme.{u}} [IsLocallyNoetherian X]
  (I : X.IdealSheafData) (M : X.Modules) [M.IsFinitePresentation] (V : X.affineOpens)

/-- The actual local ideal-action Rees module in polynomial-valued sections. -/
def affineModule : Submodule (reesAlgebra (I.ideal V))
    (PolynomialModule Γ(X, V.1) Γ(M, V.1)) :=
  ((I.ideal V).stableFiltration (⊤ : Submodule Γ(X, V.1) Γ(M, V.1))).submodule

/-- All actual power sections, without a bound on their exponent. -/
abbrev Sections := ⨁ n : ℕ, Γ(power I n M, V.1)

/-- Original power inclusions identify all degrees with the actual local Rees module. -/
def sectionsEquiv : Sections I M V ≃ₗ[Γ(X, V.1)] affineModule I M V :=
  (DirectSum.congrLinearEquiv (fun n ↦ powerAffineEquiv I n M V)).trans
    (Rees.sumEquiv ((I.ideal V).stableFiltration ⊤))

/-- Each coordinate of the equivalence is the original ideal-power inclusion. -/
lemma sectionsEquiv_coeff (s : Sections I M V) (n : ℕ) :
    (sectionsEquiv I M V s).val.coeff n = (inclusion (I ^ n) M).app V.1 (s n) := by
  exact Rees.sumEquiv_coeff ((I.ideal V).stableFiltration
    (⊤ : Submodule Γ(X, V.1) Γ(M, V.1)))
    (DirectSum.congrLinearEquiv (fun k ↦ powerAffineEquiv I k M V) s) n

/-- The actual local Rees module is finitely generated. -/
theorem affineModule_fg : (affineModule I M V).FG := by
  let _ : IsNoetherianRing Γ(X, V.1) := IsLocallyNoetherian.component_noetherian V
  let _ : Module.Finite Γ(X, V.1) Γ(M, V.1) :=
    coherentAffineOpen_sections_finite M V.2
  apply (Ideal.Filtration.submodule_fg_iff_stable _ (fun _ ↦ IsNoetherian.noetherian _)).mpr
  exact (I.ideal V).stableFiltration_stable ⊤

/-- All local power sections together form a finite module over the local Rees algebra. -/
theorem affineModule_finite : Module.Finite (reesAlgebra (I.ideal V)) (affineModule I M V) :=
  Module.Finite.of_fg (affineModule_fg I M V)

end FLT.Mazur.IdealPowerRees
