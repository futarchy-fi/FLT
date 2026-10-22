/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OneGonResidualNormalFormLifting
public import FLT.Mazur.NodeTangentCoefficientCover

/-!
# Nodal deformation normal forms on the actual tangent cover

The quadratic tangent algebra supplies the missing simple root over the original
coefficient ring. Its reduction gives a specified normalizing change, which lifts
through the extended nilpotent ideal. No rational tangent is assumed.
-/

@[expose] public noncomputable section
open WeierstrassCurve
namespace FLT.Mazur.OneGonInfinitesimal
variable {R : Type} [CommRing R] (W : WeierstrassCurve R) (I : Ideal R)
local notation "S" => AdjoinRoot (nodeTangentPolynomial W)
local notation "f" => algebraMap R S
local notation "J" => I.map f
local notation "q" => Ideal.Quotient.mk J
local notation "V" => WeierstrassCurve.map (W.map f) q
local notation "s" => q (AdjoinRoot.root (nodeTangentPolynomial W))

/-- The actual root remains a tangent root on the original infinitesimal reduction. -/
theorem tangentCover_residual_root : s ^ 2 + (V).a₁ * s = (V).a₂ := by
  have h := congrArg q (nodeTangentRoot_equation W)
  simp only [map_sub, map_add, map_pow, map_mul, map_zero, sub_eq_zero] at h
  exact h

/-- The tangent is simple on the entire reduction, including characteristic two. -/
theorem tangentCover_residual_simple (hb : IsUnit W.b₂) : IsUnit ((V).a₁ + 2 * s) := by
  simpa only [WeierstrassCurve.map, map_add, map_mul, map_ofNat] using
    (nodeTangentRoot_derivative_isUnit W hb).map q

/-- The specific residual shear and scaling constructed on the tangent cover. -/
def tangentCoverResidualChange (hb : IsUnit W.b₂) : VariableChange (S ⧸ J) :=
  splitTangentChange V s (tangentCover_residual_simple W I hb)

/-- The original reduction becomes the standard node over the quadratic cover. -/
theorem tangentCoverResidualChange_equation (hb : IsUnit W.b₂)
    (h₃ : W.a₃ ∈ I) (h₄ : W.a₄ ∈ I) (h₆ : W.a₆ ∈ I) :
    tangentCoverResidualChange W I hb • V = OneGonSmoothing.equation 0 := by
  exact splitTangentChange_equation V s (tangentCover_residual_simple W I hb)
    (tangentCover_residual_root W I)
    (Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_map_of_mem f h₃))
    (Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_map_of_mem f h₄))
    (Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_map_of_mem f h₆))

/-- A nonsplit nodal deformation has a normal form on its actual finite tangent cover. -/
theorem tangentCover_normalForm (hI : IsNilpotent I) (hb : IsUnit W.b₂)
    (h₃ : W.a₃ ∈ I) (h₄ : W.a₄ ∈ I) (h₆ : W.a₆ ∈ I) :
    ∃ (C : VariableChange S) (t : S), C • W.map f = OneGonSmoothing.equation t ∧
      C.map q = tangentCoverResidualChange W I hb ∧ t ∈ J ∧ IsUnit (1 + 432 * t) :=
  residual_normalForm_lift (W.map f) J (nilpotent_map I hI f)
    (tangentCoverResidualChange W I hb)
    (tangentCoverResidualChange_equation W I hb h₃ h₄ h₆)

/-- Only the tangent discriminant on the original reduction needs to be a unit. -/
theorem tangentCover_normalForm_of_residual_unit (hI : IsNilpotent I)
    (hb : IsUnit (Ideal.Quotient.mk I W.b₂))
    (h₃ : W.a₃ ∈ I) (h₄ : W.a₄ ∈ I) (h₆ : W.a₆ ∈ I) :
    ∃ (C : VariableChange S) (t : S), C • W.map f = OneGonSmoothing.equation t ∧
      t ∈ J ∧ IsUnit (1 + 432 * t) := by
  obtain ⟨C, t, he, _, ht, hu⟩ := tangentCover_normalForm W I hI
    (hI.isUnit_quotient_mk_iff.mp hb) h₃ h₄ h₆
  exact ⟨C, t, he, ht, hu⟩

end FLT.Mazur.OneGonInfinitesimal
