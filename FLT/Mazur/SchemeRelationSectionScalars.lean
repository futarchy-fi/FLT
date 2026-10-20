/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeEffectiveEpiSections

/-!
# Original invariant scalars on actual section rings

The equalizer of the original relation acts by restriction on every chart.
Both endpoints of an actual relation arrow induce exactly the same scalar map.
Naturality upgrades the original section pullbacks to algebra homomorphisms.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.SchemeRelationSectionScalars
open SchemeEffectiveEpiSections
set_option backward.isDefEq.respectTransparency false
variable {D A X Y : Scheme} (p q : D ⟶ A)

/-- Restriction of the original invariant scalars to an actual open section ring. -/
def scalarMap (g : X ⟶ A) (U : X.Opens) : compatibleFunctions p q →+* Γ(X, U) :=
  (g.appLE ⊤ U le_top).hom.comp (compatibleFunctions p q).subtype

/-- The scalar action is fixed by the original map, before choosing any coefficients. -/
@[instance_reducible]
def sectionAlgebra (g : X ⟶ A) (U : X.Opens) :
    Algebra (compatibleFunctions p q) Γ(X, U) := (scalarMap p q g U).toAlgebra

/-- Both full relation endpoints give the same original scalar action on every open. -/
theorem scalarMap_relation (δ : X ⟶ D) (U : X.Opens) :
    scalarMap p q (δ ≫ p) U = scalarMap p q (δ ≫ q) U := by
  ext r
  change (δ ≫ p).appLE ⊤ U le_top r.val = (δ ≫ q).appLE ⊤ U le_top r.val
  rw [Scheme.Hom.comp_appLE, Scheme.Hom.comp_appLE]
  change δ.appLE ⊤ U le_top (p.appTop r.val) =
    δ.appLE ⊤ U le_top (q.appTop r.val)
  rw [r.property]

/-- Actual section pullback commutes with restriction of every original scalar. -/
theorem scalarMap_appLE (g : X ⟶ A) (h : Y ⟶ X)
    (U : X.Opens) (V : Y.Opens) (hVU : V ≤ h ⁻¹ᵁ U) :
    (h.appLE U V hVU).hom.comp (scalarMap p q g U) = scalarMap p q (h ≫ g) V := by
  ext r
  change (g.appLE ⊤ U le_top ≫ h.appLE U V hVU) r.val = _
  rw [Scheme.Hom.appLE_comp_appLE]
  rfl

/-- A geometric source square makes the unchanged section map scalar linear. -/
def appLEAlgHom (g : X ⟶ A) (g' : Y ⟶ A) (h : Y ⟶ X)
    (hh : h ≫ g = g') (U : X.Opens) (V : Y.Opens) (hVU : V ≤ h ⁻¹ᵁ U) :
    let _ := sectionAlgebra p q g U
    let _ := sectionAlgebra p q g' V
    Γ(X, U) →ₐ[compatibleFunctions p q] Γ(Y, V) := by
  let _ := sectionAlgebra p q g U
  let _ := sectionAlgebra p q g' V
  refine { (h.appLE U V hVU).hom with commutes' := fun r ↦ ?_ }
  change ((h.appLE U V hVU).hom.comp (scalarMap p q g U)) r = scalarMap p q g' V r
  rw [scalarMap_appLE, hh]

/-- A relation square also makes the second endpoint linear for the first endpoint action. -/
def relationAppLEAlgHom (g : X ⟶ A) (g' : Y ⟶ A) (h : Y ⟶ X)
    (δ : Y ⟶ D) (hδ : δ ≫ p = g') (hδ' : δ ≫ q = h ≫ g)
    (U : X.Opens) (V : Y.Opens) (hVU : V ≤ h ⁻¹ᵁ U) :
    let _ := sectionAlgebra p q g U
    let _ := sectionAlgebra p q g' V
    Γ(X, U) →ₐ[compatibleFunctions p q] Γ(Y, V) := by
  let _ := sectionAlgebra p q g U
  let _ := sectionAlgebra p q g' V
  refine { (h.appLE U V hVU).hom with commutes' := fun r ↦ ?_ }
  change ((h.appLE U V hVU).hom.comp (scalarMap p q g U)) r = scalarMap p q g' V r
  rw [scalarMap_appLE, ← hδ', ← hδ, scalarMap_relation]

end FLT.Mazur.SchemeRelationSectionScalars
