/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.NodeTangentAlgebra

/-!
# The actual reduction of the tangent coefficient cover

Adjoining the tangent root commutes with reduction by the original ideal.
Congruent tangent coefficients therefore identify the actual reduced covers,
including their distinguished roots, without choosing quotient presentations.
-/

@[expose] public noncomputable section
open Polynomial WeierstrassCurve
namespace FLT.Mazur.OneGonInfinitesimal
variable {R : Type} [CommRing R] (W V : WeierstrassCurve R) (I : Ideal R)
local notation "q" => Ideal.Quotient.mk I
local notation "pW" => nodeTangentPolynomial W
local notation "pV" => nodeTangentPolynomial V
local notation "IW" => I.map (algebraMap R (AdjoinRoot pW))
local notation "IV" => I.map (algebraMap R (AdjoinRoot pV))

/-- Congruent tangent coefficients give the same residual polynomial. -/
theorem tangentPolynomial_reduction_eq
    (h₁ : q W.a₁ = q V.a₁) (h₂ : q W.a₂ = q V.a₂) :
    (pW).map q = (pV).map q := by
  simp only [nodeTangentPolynomial, Polynomial.map_sub, Polynomial.map_add,
    Polynomial.map_pow, Polynomial.map_mul, Polynomial.map_X, Polynomial.map_C, h₁, h₂]

/-- Identify the two actual reduced tangent algebras over the original coefficient ring. -/
def tangentReductionEquiv (h₁ : q W.a₁ = q V.a₁) (h₂ : q W.a₂ = q V.a₂) :
    (AdjoinRoot pW ⧸ IW) ≃ₐ[R] (AdjoinRoot pV ⧸ IV) :=
  (AdjoinRoot.quotEquivQuotMap pW I).trans
    ((AdjoinRoot.algEquivOfEq R ((pW).map q) ((pV).map q)
      (tangentPolynomial_reduction_eq W V I h₁ h₂)).trans
      (AdjoinRoot.quotEquivQuotMap pV I).symm)

/-- The comparison retains the original distinguished residual tangent. -/
theorem tangentReductionEquiv_root (h₁ : q W.a₁ = q V.a₁) (h₂ : q W.a₂ = q V.a₂) :
    tangentReductionEquiv W V I h₁ h₂
      (Ideal.Quotient.mk IW (AdjoinRoot.root pW)) =
        Ideal.Quotient.mk IV (AdjoinRoot.root pV) := by
  have hfirst := AdjoinRoot.quotEquivQuotMap_apply_mk pW X I
  have hlast := AdjoinRoot.quotEquivQuotMap_symm_apply_mk pV X I
  simp only [Polynomial.map_X] at hfirst hlast
  let e := AdjoinRoot.algEquivOfEq R ((pW).map q) ((pV).map q)
    (tangentPolynomial_reduction_eq W V I h₁ h₂)
  have hroot : e (AdjoinRoot.root ((pW).map q)) = AdjoinRoot.root ((pV).map q) :=
    AdjoinRoot.algEquivOfEq_root _ _ _
  exact (congrArg (fun z => (AdjoinRoot.quotEquivQuotMap pV I).symm (e z)) hfirst).trans
    ((congrArg (AdjoinRoot.quotEquivQuotMap pV I).symm hroot).trans hlast)

end FLT.Mazur.OneGonInfinitesimal
