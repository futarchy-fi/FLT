/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ModuleSheafUnitCocycle

/-!
# Comparing cocycles on equal open families

Pointwise equality of the transition units identifies their descended sheaves,
including when the two open families are only propositionally equal.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.FCurve.ModuleSheafUnitCocycle.Cocycle

universe u

variable {X : Scheme.{u}} {ι : Type u} {U V : ι → X.Opens}

/-- A cocycle is determined by its units on all common subopens. -/
theorem ext_units (g h : Cocycle U)
    (he : ∀ i j W hi hj, g.unit i j W hi hj = h.unit i j W hi hj) : g = h := by
  cases g with
  | mk gu gn gr gc =>
    cases h with
    | mk hu hn hr hc =>
      have e : gu = hu := by funext i j W hi hj; exact he i j W hi hj
      subst hu
      rfl

/-- Equal open families and equal transitions give an isomorphism of descended sheaves. -/
def sheafIsoOfUnits (g : Cocycle U) (h : Cocycle V) (hUV : ∀ i, U i = V i)
    (he : ∀ i j W hi hj, g.unit i j W hi hj =
      h.unit i j W (hi.trans (hUV i).le) (hj.trans (hUV j).le)) :
    g.sheaf ≅ h.sheaf := by
  have e : U = V := funext hUV
  subst V
  exact eqToIso (congrArg Cocycle.sheaf (ext_units g h he))

end FLT.Mazur.FCurve.ModuleSheafUnitCocycle.Cocycle
