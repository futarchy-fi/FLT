/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GrassmannianOverlapPolynomial
public import FLT.Mazur.GrassmannianChartTransition

/-!
# Rational matrix formula for Grassmannian transitions

An ambient change with blocks `(P,U; Q,T)` sends quotient coordinates `A` to
`(P + AQ)⁻¹(U + AT)`. Where the determinant is a unit, this formula preserves
all relations. It applies in particular to changes between selected ambient bases.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.GrassmannianChart
variable {S : Type*} [CommRing S] {ι κ : Type*} [Fintype ι] [Fintype κ] {d : ℕ}

/-- The ambient map with the indicated four matrix blocks. -/
def blockAmbientMap (P : Matrix (Fin d) (Fin d) S) (Q : Matrix ι (Fin d) S)
    (U : Matrix (Fin d) κ S) (T : Matrix ι κ S) :
    ((Fin d → S) × (κ → S)) →ₗ[S] ((Fin d → S) × (ι → S)) := by
  classical
  exact LinearMap.coprod (matrixSelectedSummand P Q)
    ((Matrix.toLin' U).prod (Matrix.toLin' T))

/-- The rational formula for the complementary transition matrix. -/
def blockTransitionMatrix (A : Matrix (Fin d) ι S)
    (P : Matrix (Fin d) (Fin d) S) (Q : Matrix ι (Fin d) S)
    (U : Matrix (Fin d) κ S) (T : Matrix ι κ S) : Matrix (Fin d) κ S :=
  (P + A * Q)⁻¹ * (U + A * T)

omit [Fintype κ] in
/-- Multiplying by the second basis matrix recovers the complementary image. -/
theorem blockTransitionMatrix_cancel (A : Matrix (Fin d) ι S)
    (P : Matrix (Fin d) (Fin d) S) (Q : Matrix ι (Fin d) S)
    (U : Matrix (Fin d) κ S) (T : Matrix ι κ S) (h : IsUnit (P + A * Q).det) :
    (P + A * Q) * blockTransitionMatrix A P Q U T = U + A * T :=
  Matrix.mul_nonsing_inv_cancel_left _ _ h

/-- The matrix formula factors the full ambient quotient map. -/
theorem blockTransitionMatrix_factor (A : Matrix (Fin d) ι S)
    (P : Matrix (Fin d) (Fin d) S) (Q : Matrix ι (Fin d) S)
    (U : Matrix (Fin d) κ S) (T : Matrix ι κ S) (h : IsUnit (P + A * Q).det) :
    let _ := Classical.decEq ι
    let _ := Classical.decEq κ
    (Matrix.toLin' (P + A * Q)).comp
      (splitChartEvaluation (Matrix.toLin' (blockTransitionMatrix A P Q U T))) =
        (splitChartEvaluation (Matrix.toLin' A)).comp (blockAmbientMap P Q U T) := by
  classical
  dsimp only
  have hc := congrArg (fun M : Matrix (Fin d) κ S ↦ Matrix.toLin' M)
    (blockTransitionMatrix_cancel A P Q U T h)
  rw [Matrix.toLin'_mul] at hc
  apply LinearMap.ext
  intro x
  change Matrix.toLin' (P + A * Q)
    (x.1 + Matrix.toLin' (blockTransitionMatrix A P Q U T) x.2) =
      (Matrix.toLin' P x.1 + Matrix.toLin' U x.2) +
        Matrix.toLin' A (Matrix.toLin' Q x.1 + Matrix.toLin' T x.2)
  rw [map_add, ← LinearMap.comp_apply, hc]
  simp only [map_add, Matrix.toLin'_mul, LinearMap.add_apply, LinearMap.comp_apply]
  abel

/-- The rational formula retains the entire kernel of the changed ambient quotient. -/
theorem blockTransitionMatrix_kernel (A : Matrix (Fin d) ι S)
    (P : Matrix (Fin d) (Fin d) S) (Q : Matrix ι (Fin d) S)
    (U : Matrix (Fin d) κ S) (T : Matrix ι κ S) (h : IsUnit (P + A * Q).det) :
    let _ := Classical.decEq ι
    let _ := Classical.decEq κ
    (splitChartEvaluation (Matrix.toLin' (blockTransitionMatrix A P Q U T))).ker =
      (splitChartEvaluation (Matrix.toLin' A)).ker.comap (blockAmbientMap P Q U T) := by
  classical
  dsimp only
  have hb : Function.Bijective (Matrix.toLin' (P + A * Q)) := by
    rw [← Module.End.isUnit_iff, LinearMap.isUnit_iff_isUnit_det]
    simpa only [← LinearMap.det_toMatrix', LinearMap.toMatrix'_toLin'] using h
  rw [← LinearEquiv.ker_comp (LinearEquiv.ofBijective _ hb)]
  change ((Matrix.toLin' (P + A * Q)).comp
    (splitChartEvaluation (Matrix.toLin' (blockTransitionMatrix A P Q U T)))).ker = _
  rw [blockTransitionMatrix_factor A P Q U T h]
  rfl

/-- For an ambient basis change, the rational formula is the relation-preserving transition. -/
theorem blockTransitionMatrix_eq_chartTransition (A : Matrix (Fin d) ι S)
    (P : Matrix (Fin d) (Fin d) S) (Q : Matrix ι (Fin d) S)
    (U : Matrix (Fin d) κ S) (T : Matrix ι κ S)
    (e : ((Fin d → S) × (κ → S)) ≃ₗ[S] ((Fin d → S) × (ι → S)))
    (he : e.toLinearMap = blockAmbientMap P Q U T)
    (h : IsUnit (P + A * Q).det) :
    let _ := Classical.decEq ι
    let _ := Classical.decEq κ
    ∃ hb : Function.Bijective (transitionBasis (Matrix.toLin' A) e),
      chartTransition (Matrix.toLin' A) e hb =
        Matrix.toLin' (blockTransitionMatrix A P Q U T) := by
  classical
  dsimp only
  have ht : transitionBasis (Matrix.toLin' A) e = Matrix.toLin' (P + A * Q) := by
    rw [transitionBasis, he]
    simpa only [blockAmbientMap, LinearMap.coprod_inl] using
      chartChangeMap_matrixSelected A P Q
  have hb : Function.Bijective (transitionBasis (Matrix.toLin' A) e) := by
    rw [ht, ← Module.End.isUnit_iff, LinearMap.isUnit_iff_isUnit_det]
    simpa only [← LinearMap.det_toMatrix', LinearMap.toMatrix'_toLin'] using h
  refine ⟨hb, chartTransition_unique _ _ _ _ ?_⟩
  rw [ht, he]
  exact blockTransitionMatrix_factor A P Q U T h

end FLT.Mazur.GrassmannianChart
