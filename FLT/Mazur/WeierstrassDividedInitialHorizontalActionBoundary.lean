/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedInitialConicBoundaryAlgebra
public import FLT.Mazur.WeierstrassSmoothHorizontalActionAlgebra

/-!
# The actual initial conic action retains the first line boundary

The original fraction ring is transported to its tensor localization before
using the proved initial-line identity. The resulting whole action maps keep
the next line and its signed reciprocal normalization.
-/

@[expose] public noncomputable section
open IsLocalRing Polynomial
open scoped TensorProduct LaurentPolynomial
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (D : SplitNodeDepth W π depth) (h1 : 1 ≤ n)
  (hstart : 0 < start) (hk : 2 * (start + 1) ≤ depth)
open WeierstrassModificationX WeierstrassSuccessiveX WeierstrassIntegralChart
local notation "K" => ResidueField R
local notation "d" => data (Fin.mk 0 (Nat.zero_lt_succ n))
local notation "a" => residue R W.a₁
local notation "c" => residue R (Data.b6 d)
local notation "t₀" => WeierstrassModificationX.t W (π ^ start)
  (Data.b3 d) (Data.b4 d) (Data.b6 d)
local notation "A" => K ⊗[R] WeierstrassModificationX.Coordinate W (π ^ start)
  (Data.b3 d) (Data.b4 d) (Data.b6 d)
local notation "Q" => Localization.Away ((1 : K) ⊗ₜ[R] t₀)
local notation "H" => HorizontalSourceRing W (π ^ start)
local notation "E" => horizontalReesChartEquiv W (π ^ start)
  (Data.b3 d) (Data.b4 d) (Data.b6 d) (Data.factor3 d) (Data.factor4 d)
  (Data.factor6 d) (pow_ne_zero start hπ)
local notation "tangent" => WeierstrassDilatation.residueTangentUnit D
local notation "L₁" => initialLineBoundaryMap hπ data D h1 hstart hk 0 (by simp) (tangent)⁻¹
local notation "L₂" => initialLineBoundaryMap hπ data D h1 hstart hk (-a) (by simp) (-tangent)⁻¹
local notation "f₁" => horizontalConicFirstResidue D start hstart (by omega) hπ
  (Data.b3 d) (Data.b4 d) (Data.b6 d) (Data.factor3 d) (Data.factor4 d) (Data.factor6 d)
local notation "f₂" => horizontalConicSecondResidue D start hstart (by omega) hπ
  (Data.b3 d) (Data.b4 d) (Data.b6 d) (Data.factor3 d) (Data.factor4 d) (Data.factor6 d)

/-- The original horizontal functions on the actual localized initial tensor chart. -/
def initialHorizontalBoundaryInput : H →ₐ[R] Q :=
  (IsScalarTower.toAlgHom R A Q).comp
    (Algebra.TensorProduct.includeRight.comp (E).symm.toAlgHom)

/-- The first original fraction puncture is the retained next line with reciprocal scale. -/
theorem initialHorizontalFirstResidue_boundary :
    f₁ = ((L₁).restrictScalars R).comp (initialHorizontalBoundaryInput hπ data) := by
  apply AlgHom.ext
  intro q
  have h := AlgHom.congr_fun (initialConicFirstLine_algebra hπ data D h1 hstart hk)
    ((1 : K) ⊗ₜ[R] (E).symm q)
  exact h.symm

/-- The opposite original puncture retains the negative reciprocal line normalization. -/
theorem initialHorizontalSecondResidue_boundary :
    f₂ = ((L₂).restrictScalars R).comp (initialHorizontalBoundaryInput hπ data) := by
  apply AlgHom.ext
  intro q
  have h := AlgHom.congr_fun (initialConicSecondLine_algebra hπ data D h1 hstart hk)
    ((1 : K) ⊗ₜ[R] (E).symm q)
  exact h.symm

local notation "τ" => smoothHorizontalTangentUnit D
local notation "z" => smoothHorizontalConicUnit D
local notation "q₁" => smoothHorizontalLaurentEvaluation D (τ * z)
local notation "q₂" => smoothHorizontalLaurentEvaluation D (τ⁻¹ * z)

/-- The genuine first action agrees on every original function with the scaled line boundary. -/
theorem initialHorizontalFirstAction_boundary :
    smoothHorizontalFirstAction (k := start) D d hstart (by omega) hπ =
      ((q₁).restrictScalars R).comp
        (((L₁).restrictScalars R).comp (initialHorizontalBoundaryInput hπ data)) := by
  refine (smoothHorizontalFirstAction_eq (k := start) D d hstart (by omega) hπ).trans ?_
  exact congrArg (fun f => ((q₁).restrictScalars R).comp f)
    (initialHorizontalFirstResidue_boundary hπ data D h1 hstart hk)

/-- The genuine opposite action keeps the same retained line with its opposite character. -/
theorem initialHorizontalSecondAction_boundary :
    smoothHorizontalSecondAction (k := start) D d hstart (by omega) hπ =
      ((q₂).restrictScalars R).comp
        (((L₂).restrictScalars R).comp (initialHorizontalBoundaryInput hπ data)) := by
  refine (smoothHorizontalSecondAction_eq (k := start) D d hstart (by omega) hπ).trans ?_
  exact congrArg (fun f => ((q₂).restrictScalars R).comp f)
    (initialHorizontalSecondResidue_boundary hπ data D h1 hstart hk)

end FLT.Mazur.WeierstrassDividedDepth
