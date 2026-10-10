/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.BaseAdicReesChart
public import FLT.Mazur.IdealPowerReesChart
public import FLT.Mazur.ReesRelativeModuleMap

/-!
# Actual chart restrictions for relative Rees models

The original structure morphism makes chart restrictions base-linear.
The relative tensor rings and their actual extended-power modules restrict
compatibly, and the coordinates retain all original power-section maps.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry
open Scheme.Modules FLT.Mazur.BaseAdicThickening FLT.Mazur.GlobalIdealPower
open scoped TensorProduct

universe u

namespace FLT.Mazur.BaseAdicRees

variable {R : CommRingCat.{u}} {X : Scheme.{u}} (f : X ⟶ Spec R)
  (J : Ideal R) {U V W : X.affineOpens}

/-- The actual structure-sheaf restriction is linear over the original base ring. -/
def chartRingRestriction (h : U.1 ≤ V.1) :
    let _ := chartAlgebra f V
    let _ := chartAlgebra f U
    Γ(X, V.1) →ₐ[R] Γ(X, U.1) := by
  let _ := chartAlgebra f V
  let _ := chartAlgebra f U
  refine
    { toRingHom := (X.presheaf.map (homOfLE h).op).hom
      commutes' := ?_ }
  intro r
  change X.presheaf.map (homOfLE h).op (chartScalars f V r) = chartScalars f U r
  simp only [chartScalars, RingHom.comp_apply, ← CommRingCat.comp_apply,
    Category.assoc, Scheme.Hom.appLE_map]

/-- Restriction of the actual relative tensor coordinate rings. -/
def relativeRingRestriction (h : U.1 ≤ V.1) :
    let _ := chartAlgebra f V
    let _ := chartAlgebra f U
    Γ(X, V.1) ⊗[R] reesAlgebra J →ₐ[R] Γ(X, U.1) ⊗[R] reesAlgebra J := by
  let _ := chartAlgebra f V
  let _ := chartAlgebra f U
  exact Rees.relativeAlgebraMap J (chartRingRestriction f h)

variable (M : X.Modules)

/-- Actual section restriction on the relative Rees modules. -/
def relativeRestriction (h : U.1 ≤ V.1) :
    let _ := chartAlgebra f V
    let _ := chartAlgebra f U
    let _ := Rees.relativeModule (S := Γ(X, V.1)) (M := Γ(M, V.1)) J
    let _ := Rees.relativeModule (S := Γ(X, U.1)) (M := Γ(M, U.1)) J
    Rees.extendedModule (S := Γ(X, V.1)) (M := Γ(M, V.1)) J →ₛₗ[
      (relativeRingRestriction f J h).toRingHom]
      Rees.extendedModule (S := Γ(X, U.1)) (M := Γ(M, U.1)) J := by
  let _ := chartAlgebra f V
  let _ := chartAlgebra f U
  exact Rees.relativeModuleMap J (chartRingRestriction f h)
    (IdealPowerRees.sectionRestriction M h)

/-- Every relative polynomial coefficient is the original sheaf restriction. -/
lemma relativeRestriction_coeff (h : U.1 ≤ V.1)
    (s : let _ := chartAlgebra f V
      Rees.extendedModule (S := Γ(X, V.1)) (M := Γ(M, V.1)) J) (n : ℕ) :
    (relativeRestriction f J M h s).val.coeff n =
      M.presheaf.map (homOfLE h).op (s.val.coeff n) := rfl

variable [IsLocallyNoetherian X] [M.IsFinitePresentation]

/-- Relative affine coordinates intertwine all original ideal-power section restrictions. -/
lemma sectionsEquiv_restriction (h : U.1 ≤ V.1)
    (s : IdealPowerRees.Sections ((baseIdeal R J).comap f) M V) :
    sectionsEquiv f J U M
      (IdealPowerRees.chartRestriction _ M V h le_rfl (homOfLE h) s) =
      relativeRestriction f J M h (sectionsEquiv f J V M s) := by
  apply Subtype.ext
  ext n
  rw [sectionsEquiv_coeff, relativeRestriction_coeff, sectionsEquiv_coeff]
  exact congr($((inclusion (((baseIdeal R J).comap f) ^ n) M).val.naturality
    (homOfLE h).op) (s n))

end FLT.Mazur.BaseAdicRees
