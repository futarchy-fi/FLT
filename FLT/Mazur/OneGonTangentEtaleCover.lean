/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.NodeTangentCoefficientCover
public import FLT.Mazur.NodeTangentUnramified
public import Mathlib.RingTheory.Etale.StandardEtale
public import Mathlib.AlgebraicGeometry.Morphisms.Etale

/-!
# An etale tangent cover for ordinary nodal deformations

Invertibility of the tangent discriminant makes the actual quadratic root
algebra etale. The derivative localization is already the entire root algebra,
so the existing finite faithfully flat cover is an etale surjection.
-/

@[expose] public noncomputable section
open Polynomial AlgebraicGeometry
namespace FLT.Mazur.OneGonInfinitesimal
variable {R : Type} [CommRing R] (W : WeierstrassCurve R)
local notation "poly" => nodeTangentPolynomial W
local notation "A" => AdjoinRoot poly

/-- The tangent quadratic with its derivative defines a standard etale pair. -/
def tangentEtalePair : StandardEtalePair R where
  f := poly
  monic_f := nodeTangentPolynomial_monic W
  g := Polynomial.derivative poly
  cond := ⟨1, 0, 1, by simp⟩

/-- Over the ordinary node locus the derivative localization is the whole tangent algebra. -/
def tangentDerivativeLocalizationIso (hb : IsUnit W.b₂) :
    A ≃ₐ[R] Localization.Away (AdjoinRoot.mk poly (poly).derivative) := by
  have hu : IsUnit (AdjoinRoot.mk poly (poly).derivative) := by
    rw [← AdjoinRoot.aeval_eq, nodeTangentPolynomial_aeval_derivative]
    exact nodeTangentRoot_derivative_isUnit W hb
  exact (IsLocalization.atUnits A (Submonoid.powers (AdjoinRoot.mk poly (poly).derivative))
    (S := Localization.Away (AdjoinRoot.mk poly (poly).derivative))
    (Submonoid.powers_le.mpr hu)).restrictScalars R

/-- The actual finite quadratic tangent algebra is etale, without any characteristic bound. -/
theorem tangentAlgebra_etale (hb : IsUnit W.b₂) : Algebra.Etale R A := by
  let _ : Algebra.Etale R (Localization.Away (AdjoinRoot.mk poly (poly).derivative)) :=
    Algebra.Etale.of_equiv (tangentEtalePair W).equivAwayAdjoinRoot
  exact Algebra.Etale.of_equiv (tangentDerivativeLocalizationIso W hb).symm

/-- The original coefficient morphism is an etale surjection. -/
theorem tangentCover_etale_surjective [Nontrivial R] (hb : IsUnit W.b₂) :
    Etale (nodeTangentCover W) ∧ Surjective (nodeTangentCover W) := by
  refine ⟨?_, (nodeTangentCover_flat_surjective W).2⟩
  exact (HasRingHomProperty.Spec_iff (P := @Etale)).mpr
    (RingHom.etale_algebraMap.mpr (tangentAlgebra_etale W hb))

end FLT.Mazur.OneGonInfinitesimal
