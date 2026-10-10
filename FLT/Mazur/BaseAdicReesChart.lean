/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.BaseAdicThickening
public import FLT.Mazur.IdealPowerReesSections
public import FLT.Mazur.ReesAffineModel
public import FLT.Mazur.ReesModuleIdealCongr

/-!
# Relative Rees models for the actual extended base ideal

Each source chart carries the scalar map of the original structure morphism.
Its actual power sections identify with the extended-ideal Rees module over
that chart, and define a coherent sheaf on the relative affine spectrum.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry
open Scheme.Modules FLT.Mazur.BaseAdicThickening FLT.Mazur.IdealPowerRees
open scoped TensorProduct

universe u

namespace FLT.Mazur.BaseAdicRees

variable {R : CommRingCat.{u}} {X : Scheme.{u}} (f : X ⟶ Spec R)
  (J : Ideal R) (V : X.affineOpens)

/-- The chart scalar map induced by the original structure morphism. -/
def chartScalars : R →+* Γ(X, V.1) :=
  (f.appLE ⊤ V.1 (by simp)).hom.comp (Scheme.ΓSpecIso R).inv.hom

/-- The actual base algebra structure on the chart coordinate ring. -/
@[instance_reducible]
def chartAlgebra : Algebra R Γ(X, V.1) := (chartScalars f V).toAlgebra

/-- The chart ideal is precisely extension along the actual structure map. -/
lemma chartIdeal_eq :
    let _ := chartAlgebra f V
    ((baseIdeal R J).comap f).ideal V = J.map (algebraMap R Γ(X, V.1)) := by
  change ((baseIdeal R J).comap f).ideal V = J.map (chartScalars f V)
  simpa only [pow_one, chartScalars] using extendedPower_ideal J f V 1

variable [IsLocallyNoetherian X] (M : X.Modules) [M.IsFinitePresentation]

/-- The polynomial modules have the same coefficients in the same ideal powers. -/
def affineModuleEquiv :
    let _ := chartAlgebra f V
    affineModule ((baseIdeal R J).comap f) M V ≃ₗ[Γ(X, V.1)]
    Rees.extendedModule (S := Γ(X, V.1)) (M := Γ(M, V.1)) J := by
  let _ := chartAlgebra f V
  exact Rees.powerModuleCongr _ _ (chartIdeal_eq f J V)

omit [IsLocallyNoetherian X] [M.IsFinitePresentation] in
/-- The comparison preserves the original polynomial, not only its isomorphism class. -/
lemma affineModuleEquiv_val (s : affineModule ((baseIdeal R J).comap f) M V) :
    (affineModuleEquiv f J V M s).val = s.val :=
  Rees.powerModuleCongr_val _ _ (chartIdeal_eq f J V) s

/-- Original power sections give coordinates for the actual relative Rees model. -/
def sectionsEquiv :
    let _ := chartAlgebra f V
    IdealPowerRees.Sections ((baseIdeal R J).comap f) M V ≃ₗ[Γ(X, V.1)]
    Rees.extendedModule (S := Γ(X, V.1)) (M := Γ(M, V.1)) J := by
  let _ := chartAlgebra f V
  exact (IdealPowerRees.sectionsEquiv _ M V).trans (affineModuleEquiv f J V M)

/-- These coordinates retain the original ideal-power inclusion in every degree. -/
lemma sectionsEquiv_coeff (s : IdealPowerRees.Sections ((baseIdeal R J).comap f) M V) (n : ℕ) :
    (sectionsEquiv f J V M s).val.coeff n =
      (GlobalIdealPower.inclusion (((baseIdeal R J).comap f) ^ n) M).app V.1 (s n) := by
  change (affineModuleEquiv f J V M (IdealPowerRees.sectionsEquiv _ M V s)).val.coeff n = _
  rw [affineModuleEquiv_val, IdealPowerRees.sectionsEquiv_coeff]

/-- Finiteness over the relative chart ring uses the actual quotient Rees comparison. -/
theorem relativeModule_finite :
    let _ := chartAlgebra f V
    let _ := Rees.relativeModule (S := Γ(X, V.1)) (M := Γ(M, V.1)) J
    Module.Finite (Γ(X, V.1) ⊗[R] reesAlgebra J)
      (Rees.extendedModule (S := Γ(X, V.1)) (M := Γ(M, V.1)) J) := by
  let _ := chartAlgebra f V
  let _ := IsLocallyNoetherian.component_noetherian V
  let _ : Module.Finite Γ(X, V.1) Γ(M, V.1) :=
    FCurve.coherentAffineOpen_sections_finite M V.2
  exact Rees.relativeModule_finite J

variable [IsNoetherianRing R]

/-- The coherent affine relative model of all actual extended-ideal power sections. -/
def modelSheaf :
    let _ := chartAlgebra f V
    (Spec (.of (Γ(X, V.1) ⊗[R] reesAlgebra J))).Modules := by
  let _ := chartAlgebra f V
  let _ := IsLocallyNoetherian.component_noetherian V
  let _ : Module.Finite Γ(X, V.1) Γ(M, V.1) :=
    FCurve.coherentAffineOpen_sections_finite M V.2
  exact Rees.affineModuleSheaf (S := Γ(X, V.1)) J Γ(M, V.1)

/-- The actual relative model is coherent. -/
instance modelSheaf_isFinitePresentation : (modelSheaf f J V M).IsFinitePresentation := by
  let _ := chartAlgebra f V
  let _ := IsLocallyNoetherian.component_noetherian V
  let _ : Module.Finite Γ(X, V.1) Γ(M, V.1) :=
    FCurve.coherentAffineOpen_sections_finite M V.2
  exact Rees.affineModuleSheaf_isFinitePresentation J Γ(M, V.1)

end FLT.Mazur.BaseAdicRees
