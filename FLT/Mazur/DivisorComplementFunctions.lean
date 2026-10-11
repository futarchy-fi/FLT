/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.DivisorSectionComplement
public import FLT.Mazur.SectionGradedLocalCoordinates
public import Mathlib.Tactic.IrreducibleDef

/-!
# Actual pole sections as functions on the divisor complement

The inverse canonical section trivializes the divisor line off its support.
Its tensor-power coordinates send products of sections to products of regular functions.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
namespace FLT.Mazur.FCurve
open ModuleLineBundleTensorPullback
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {X : Scheme.{u}} {I : X.IdealSheafData} (hI : EffectiveCartier I)

/-- Trivialize the original divisor line by its canonical section on the complement. -/
irreducible_def divisorComplementTrivialization :
    (divisorLineBundle I hI).restrict (Scheme.Opens.ι (X := X) I.support.compl) ≅
      structureModule (Scheme.Opens.toScheme (X := X) I.support.compl) := by
  let _ := divisorSection_isIso_complement hI
  exact (asIso (sectionHom _ _ (divisorSection hI I.support.compl))).symm

/-- A global pole section gives a regular function on the actual divisor complement. -/
def divisorComplementFunction (m : ℕ)
    (s : Γ(tensorPower (divisorLineBundle I hI) m, ⊤)) :
    Γ((Scheme.Opens.toScheme (X := X) I.support.compl), ⊤) :=
  SectionGradedLocalCoordinates.coordinate (divisorComplementTrivialization hI) m ⊤
    ((tensorPower (divisorLineBundle I hI) m).presheaf.map
      (homOfLE (show (Scheme.Opens.ι (X := X) I.support.compl) ''ᵁ ⊤ ≤ ⊤ from le_top)).op s)

/-- The function of a product is the product of the two functions. -/
theorem divisorComplementFunction_mul (m n : ℕ)
    (s : Γ(tensorPower (divisorLineBundle I hI) m, ⊤))
    (t : Γ(tensorPower (divisorLineBundle I hI) n, ⊤)) :
    divisorComplementFunction hI (m + n)
      (SectionGradedMultiplication.mul (divisorLineBundle I hI) ⊤ m n s t) =
        divisorComplementFunction hI m s * divisorComplementFunction hI n t := by
  unfold divisorComplementFunction
  rw [SectionGradedMultiplication.mul_restrict,
    SectionGradedLocalCoordinates.coordinate_mul]

/-- Addition of pole sections becomes addition of regular functions. -/
theorem divisorComplementFunction_add (m : ℕ)
    (s t : Γ(tensorPower (divisorLineBundle I hI) m, ⊤)) :
    divisorComplementFunction hI m (s + t) =
      divisorComplementFunction hI m s + divisorComplementFunction hI m t := by
  unfold divisorComplementFunction SectionGradedLocalCoordinates.coordinate
  simp only [map_add]

/-- The zero section gives the zero function. -/
theorem divisorComplementFunction_zero (m : ℕ) :
    divisorComplementFunction hI m 0 = 0 := by
  unfold divisorComplementFunction SectionGradedLocalCoordinates.coordinate
  simp only [map_zero]

end FLT.Mazur.FCurve
