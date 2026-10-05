/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticPointMapCoordinates
public import FLT.Mazur.EllipticNodeGaloisLabel

/-!
# Fixed points after an integral shear

An explicit conjugation equation for the shear parameter makes the
semilinear tangent action fix points whose original coordinates are fixed.
All maps here act on actual nonsingular points.
-/

@[expose] public section

namespace FLT.Mazur

open WeierstrassCurve

variable {L : Type*} [Field L]
  (B : ValuationSubring L) (V : WeierstrassCurve B) (s : B)

/-- The unit shear with parameter s. -/
def integralRootShear : VariableChange B := ⟨1, 0, s, 0⟩

/-- Inverse shearing preserves nonsingularity at the explicit coordinates. -/
theorem integralRootShear_nonsingular {x y : L}
    (h : (V.map (algebraMap B L)).toAffine.Nonsingular x y) :
    (((integralRootShear B s • V).map (algebraMap B L))).toAffine.Nonsingular
      x (y - s * x) := by
  rw [← map_variableChange]
  apply (variableChange_nonsingular _ _ _ _).mp
  simpa [integralRootShear, VariableChange.map] using h

variable [DecidableEq L] [(V.map (algebraMap B L)).IsElliptic]

/-- Inverse shearing on actual projective points subtracts sx from y. -/
theorem integralRootShear_symm_some {x y : L}
    (h : (V.map (algebraMap B L)).toAffine.Nonsingular x y) :
    (integralProjectiveVariableChange B V (integralRootShear B s)).symm
        (Affine.Point.some x y h).toProjective =
      (Affine.Point.some x (y - s * x) (integralRootShear_nonsingular B V s h)).toProjective := by
  apply (integralProjectiveVariableChange B V (integralRootShear B s)).injective
  rw [AddEquiv.apply_symm_apply]
  have ht : (V.map (algebraMap B L)).toAffine.Nonsingular
      (((integralRootShear B s).u : L) ^ 2 * x + (integralRootShear B s).r)
      (((integralRootShear B s).u : L) ^ 3 * (y - s * x) +
        ((integralRootShear B s).u : L) ^ 2 * (integralRootShear B s).s * x +
        (integralRootShear B s).t) := by
    simpa [integralRootShear] using h
  rw [integralProjectiveVariableChange_some B V _ _ ht]
  apply congrArg Affine.Point.toProjective
  apply Affine.Point.some_eq_some <;> simp [integralRootShear]

variable (σ : L →+* L) (τ : B →+* B)
  (hc : (algebraMap B L).comp τ = σ.comp (algebraMap B L))
  (he : (integralRootShear B s • V).map τ =
    nodeTangentSwap (integralRootShear B s • V) • (integralRootShear B s • V))
  [((integralRootShear B s • V).map (algebraMap B L)).IsElliptic]

/-- Conjugation followed by tangent exchange fixes the inverse shear of a fixed affine point. -/
theorem nodeGaloisPointAction_fixed_shear_some
    (hs : σ (s : L) = (s : L) - ((integralRootShear B s • V).a₁ : L))
    {x y : L} (hx : σ x = x) (hy : σ y = y)
    (h : (V.map (algebraMap B L)).toAffine.Nonsingular x y) :
    nodeGaloisPointAction B (integralRootShear B s • V) σ τ hc he
        ((integralProjectiveVariableChange B V (integralRootShear B s)).symm
          (Affine.Point.some x y h).toProjective) =
      (integralProjectiveVariableChange B V (integralRootShear B s)).symm
        (Affine.Point.some x y h).toProjective := by
  rw [integralRootShear_symm_some]
  let S := integralRootShear B s • V
  have hq := integralRootShear_nonsingular B V s h
  have heq := nodeGaloisEquation B S σ τ hc he
  have hext := extension_nonsingular _ σ _ heq hq
  have hX : (((nodeTangentSwap S).u : L) ^ 2 * σ x + (nodeTangentSwap S).r) = x := by
    simp [nodeTangentSwap, hx]
  have hY : (((nodeTangentSwap S).u : L) ^ 3 * σ (y - s * x) +
      ((nodeTangentSwap S).u : L) ^ 2 * (nodeTangentSwap S).s * σ x +
      (nodeTangentSwap S).t) = y - s * x := by
    simp [nodeTangentSwap, hx, hy, hs]
    dsimp [S]
    ring
  have ht : (S.map (algebraMap B L)).toAffine.Nonsingular
      (((nodeTangentSwap S).u : L) ^ 2 * σ x + (nodeTangentSwap S).r)
      (((nodeTangentSwap S).u : L) ^ 3 * σ (y - s * x) +
        ((nodeTangentSwap S).u : L) ^ 2 * (nodeTangentSwap S).s * σ x +
        (nodeTangentSwap S).t) := by rw [hX, hY]; exact hq
  change integralProjectiveVariableChange B S (nodeTangentSwap S)
    (extensionProjectiveHom _ σ _ heq _) = _
  rw [extensionProjectiveHom_some _ σ _ heq hq hext,
    integralProjectiveVariableChange_some B S _ hext ht]
  apply congrArg Affine.Point.toProjective
  exact Affine.Point.some_eq_some _ hX hY

/-- Every extended point from a field fixed by σ is fixed after the inverse shear. -/
theorem nodeGaloisPointAction_fixed_shear_extension
    (hs : σ (s : L) = (s : L) - ((integralRootShear B s • V).a₁ : L))
    {K : Type*} [Field K] (W : WeierstrassCurve K) (f : K →+* L)
    (hf : ∀ x, σ (f x) = f x) (hV : W.map f = V.map (algebraMap B L))
    (P : W.toProjective.Point) :
    nodeGaloisPointAction B (integralRootShear B s • V) σ τ hc he
        ((integralProjectiveVariableChange B V (integralRootShear B s)).symm
          (extensionProjectiveHom W f _ hV P)) =
      (integralProjectiveVariableChange B V (integralRootShear B s)).symm
        (extensionProjectiveHom W f _ hV P) := by
  classical
  obtain ⟨p, rfl⟩ := (Projective.Point.toAffineAddEquiv W.toProjective).symm.surjective P
  simp only [Projective.Point.toAffineAddEquiv_symm_apply]
  cases p with
  | zero =>
    change nodeGaloisPointAction _ _ _ _ _ _
      ((integralProjectiveVariableChange _ _ _).symm
        (extensionProjectiveHom _ _ _ _ 0)) = _
    simp only [← Affine.Point.zero_def, Projective.Point.fromAffine_zero, map_zero]
  | some x y h =>
    change nodeGaloisPointAction _ _ _ _ _ _
      ((integralProjectiveVariableChange _ _ _).symm
        (extensionProjectiveHom _ _ _ _ (Affine.Point.some x y h).toProjective)) = _
    rw [extensionProjectiveHom_some W f _ hV h (extension_nonsingular W f _ hV h)]
    exact nodeGaloisPointAction_fixed_shear_some B V s σ τ hc he hs (hf x) (hf y) _

end FLT.Mazur
