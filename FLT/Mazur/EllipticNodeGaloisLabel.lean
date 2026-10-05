/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticNodeLabelBaseChange
public import FLT.Mazur.EllipticNodeTangentSwapLabel

/-!
# Semilinear tangent exchange on actual component labels

A compatible field and local coefficient map conjugating the equation to its
tangent swap acts on the original point group by extension followed by the
actual coordinate shear. This action negates the canonical component label.
-/

@[expose] public section

namespace FLT.Mazur

open WeierstrassCurve

variable {K : Type*} [Field K] [DecidableEq K]
  (A : ValuationSubring K) (W : WeierstrassCurve A)
  (σ : K →+* K) (τ : A →+* A) [IsLocalHom τ]
  (hc : (algebraMap A K).comp τ = σ.comp (algebraMap A K))
  (he : W.map τ = nodeTangentSwap W • W)

include hc he

omit [DecidableEq K] [IsLocalHom τ] in
/-- The conjugated generic equation is the generic tangent-swap equation. -/
theorem nodeGaloisEquation :
    (W.map (algebraMap A K)).map σ =
      (nodeTangentSwap W • W).map (algebraMap A K) := by
  rw [map_map, ← hc, ← map_map, he]

variable [(W.map (algebraMap A K)).IsElliptic]

/-- Coordinate extension followed by tangent exchange is an actual point-group map. -/
noncomputable def nodeGaloisPointAction :
    (W.map (algebraMap A K)).toProjective.Point →+
      (W.map (algebraMap A K)).toProjective.Point :=
  (integralProjectiveVariableChange A W (nodeTangentSwap W)).toAddMonoidHom.comp
    (extensionProjectiveHom _ σ _ (nodeGaloisEquation A W σ τ hc he))

/-- Semilinear tangent exchange negates the signed depth of every actual point. -/
theorem nodePointLabel_galois {π : A} {n : ℕ} (D : SplitNodeDepth W π n)
    (hπ : τ π = π) (P : (W.map (algebraMap A K)).toProjective.Point) :
    nodePointLabel D (nodeGaloisPointAction A W σ τ hc he P) = -nodePointLabel D P := by
  change nodePointLabel D (integralProjectiveVariableChange A W (nodeTangentSwap W) _) = _
  rw [nodePointLabel_tangentSwap D]
  congr 1
  have D' : SplitNodeDepth (nodeTangentSwap W • W) (τ π) n := by
    rw [hπ]
    exact D.tangentSwap W
  simpa only [hπ] using
    nodePointLabel_extensionProjectiveHom A A W σ τ hc D D' he P

/-- The semilinear action preserves the actual smooth-reduction subgroup. -/
theorem nodeGaloisPointAction_smooth {π : A} {n : ℕ} (D : SplitNodeDepth W π n)
    (hπ : τ π = π) (P : (W.map (algebraMap A K)).toProjective.Point) :
    SmoothReduction A W (nodeGaloisPointAction A W σ τ hc he P) ↔
      SmoothReduction A W P := by
  rw [← nodePointLabel_eq_zero_iff D, nodePointLabel_galois A W σ τ hc he D hπ,
    neg_eq_zero, nodePointLabel_eq_zero_iff D]

/-- Semilinear tangent exchange descends to the actual component quotient. -/
noncomputable def nodeGaloisComponentAction {π : A} {n : ℕ} (D : SplitNodeDepth W π n)
    (hπ : τ π = π) : EllipticComponentQuotient A W →+ EllipticComponentQuotient A W :=
  QuotientAddGroup.map (ellipticE0 A W) (ellipticE0 A W)
    (nodeGaloisPointAction A W σ τ hc he)
    (fun P hP => (nodeGaloisPointAction_smooth A W σ τ hc he D hπ P).mpr hP)

/-- The component action is induced by the explicitly constructed point action. -/
theorem nodeGaloisComponentAction_mk {π : A} {n : ℕ} (D : SplitNodeDepth W π n)
    (hπ : τ π = π) (P : (W.map (algebraMap A K)).toProjective.Point) :
    nodeGaloisComponentAction A W σ τ hc he D hπ (ellipticComponentHom A W P) =
      ellipticComponentHom A W (nodeGaloisPointAction A W σ τ hc he P) := rfl

/-- The actual component action negates labels, with no assumed Galois action on labels. -/
theorem nodeComponentLabel_galois {π : A} {n : ℕ} (D : SplitNodeDepth W π n)
    (hπ : τ π = π) (c : EllipticComponentQuotient A W) :
    nodeComponentLabel D (nodeGaloisComponentAction A W σ τ hc he D hπ c) =
      -nodeComponentLabel D c := by
  obtain ⟨P, rfl⟩ := ellipticComponentHom_surjective A W c
  rw [nodeGaloisComponentAction_mk, nodeComponentLabel_mk, nodeComponentLabel_mk]
  exact nodePointLabel_galois A W σ τ hc he D hπ P

end FLT.Mazur
