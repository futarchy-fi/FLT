/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.NodeTangentGaloisLabel
public import FLT.Mazur.EllipticShearDescent

/-!
# The realized tangent model is an explicit integral shear

Identify the realized root and shear, and prove their conjugation formulas.
These identities connect the general fixed-point calculation with the
canonical tangent extension.
-/

@[expose] public section

namespace FLT.Mazur

open WeierstrassCurve

variable {K : Type*} [Field K] (A : ValuationSubring K) (W : WeierstrassCurve A)
  (L : Type*) [Field L]
  [IsDomain (AdjoinRoot (nodeTangentPolynomial W))]
  [IsDiscreteValuationRing (AdjoinRoot (nodeTangentPolynomial W))]
  [Algebra (AdjoinRoot (nodeTangentPolynomial W)) L]
  [IsFractionRing (AdjoinRoot (nodeTangentPolynomial W)) L]

/-- The distinguished tangent root in the actual valuation subring. -/
noncomputable def nodeTangentValuationRoot : nodeTangentValuationSubring A W L :=
  nodeTangentValuationEquiv A W L (AdjoinRoot.root (nodeTangentPolynomial W))

/-- The realized tangent model is the root shear of the unsheared base change. -/
theorem nodeTangentValuationShear_eq_rootShear :
    nodeTangentValuationShear A W L =
      integralRootShear (nodeTangentValuationSubring A W L) (nodeTangentValuationRoot A W L) •
        W.map (nodeTangentValuationBaseMap A W L) := by
  unfold nodeTangentValuationShear nodeTangentShear
  rw [← map_variableChange, map_map]
  congr 1
  ext <;> simp [integralRootShear, nodeTangentValuationRoot, VariableChange.map]

/-- The coefficient a₁ of the realized shear is a₁ + 2s. -/
theorem nodeTangentValuationShear_a₁ :
    (nodeTangentValuationShear A W L).a₁ = nodeTangentValuationBaseMap A W L W.a₁ +
      2 * nodeTangentValuationRoot A W L := by
  rw [nodeTangentValuationShear_eq_rootShear]
  simp [integralRootShear, variableChange_a₁]

/-- Integral conjugation sends the realized root to the other root. -/
theorem nodeTangentValuationRoot_conjugate :
    nodeTangentValuationConjugation A W L (nodeTangentValuationRoot A W L) =
      -nodeTangentValuationBaseMap A W L W.a₁ - nodeTangentValuationRoot A W L := by
  rw [nodeTangentValuationRoot, nodeTangentValuationConjugation_equiv]
  change nodeTangentValuationEquiv A W L
    ((nodeTangentConjugationHom W) (AdjoinRoot.root (nodeTangentPolynomial W))) = _
  rw [nodeTangentConjugationHom_root, map_sub, map_neg]
  rfl

variable [Algebra A L] [IsScalarTower A (AdjoinRoot (nodeTangentPolynomial W)) L]
  [Algebra K L] [IsScalarTower A K L]

/-- The generic root conjugation satisfies the exact fixed-shear coordinate identity. -/
theorem nodeTangentValuationRoot_field_conjugate :
    nodeTangentFieldConjugation A W L (nodeTangentValuationRoot A W L : L) =
      (nodeTangentValuationRoot A W L : L) - ((nodeTangentValuationShear A W L).a₁ : L) := by
  rw [nodeTangentFieldConjugation_coe, nodeTangentValuationRoot_conjugate,
    nodeTangentValuationShear_a₁]
  have h : -nodeTangentValuationBaseMap A W L W.a₁ - nodeTangentValuationRoot A W L =
      nodeTangentValuationRoot A W L - (nodeTangentValuationBaseMap A W L W.a₁ +
        2 * nodeTangentValuationRoot A W L) := by ring
  exact (congrArg (fun z : nodeTangentValuationSubring A W L => (z : L)) h).trans
    ((nodeTangentValuationSubring A W L).subtype.map_sub _ _)

end FLT.Mazur
