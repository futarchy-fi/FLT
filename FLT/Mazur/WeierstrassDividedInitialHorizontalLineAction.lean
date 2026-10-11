/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedInitialHorizontalActionBoundary
public import FLT.Mazur.WeierstrassSmoothHorizontalReciprocalCharacters

/-!
# Whole initial action maps in the retained next-line coordinate

Transport through the original initial overlap before restricting to the
next line. Its positive branch coordinate has character tau inverse and its
opposite coordinate has character tau, including the original tangent signs.
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

local notation "x₀" => WeierstrassDilatation.x W (π ^ start)
  (Data.b3 d) (Data.b4 d) (Data.b6 d)
local notation "transition" => PrincipalOpenTensor.transition K x₀ t₀
  (overlapEquiv W (π ^ start) (Data.b3 d) (Data.b4 d) (Data.b6 d))
local notation "N₁" => residueFiniteLineBoundaryMap hπ data D 0 h1 hstart hk 0 (by simp)
local notation "N₂" => residueFiniteLineBoundaryMap hπ data D 0 h1 hstart hk (-a) (by simp)
local notation "τ" => smoothHorizontalTangentUnit D
local notation "z" => smoothHorizontalConicUnit D
local notation "C" => SmoothHorizontalResidueRing D
local notation "j" => Units.map (algebraMap K C)

/-- Original horizontal functions restricted to the actual next line before reciprocal scaling. -/
def initialHorizontalFirstLineRestriction : H →ₐ[R] K[T;T⁻¹] :=
  ((N₁).restrictScalars R).comp
    (((transition).symm.toAlgHom.restrictScalars R).comp
      (initialHorizontalBoundaryInput hπ data))

/-- The corresponding restriction on the original opposite retained line. -/
def initialHorizontalSecondLineRestriction : H →ₐ[R] K[T;T⁻¹] :=
  ((N₂).restrictScalars R).comp
    (((transition).symm.toAlgHom.restrictScalars R).comp
      (initialHorizontalBoundaryInput hπ data))

set_option maxRecDepth 2048 in
/-- The first actual action has the inverse character in the retained next-line coordinate. -/
theorem initialHorizontalFirstAction_line :
    smoothHorizontalFirstAction (k := start) D d hstart (by omega) hπ =
      ((smoothHorizontalLaurentEvaluation D (τ⁻¹ * (j tangent⁻¹ * z⁻¹))).restrictScalars R).comp
        (initialHorizontalFirstLineRestriction hπ data D h1 hstart hk) := by
  apply AlgHom.ext
  intro q
  have h := AlgHom.congr_fun (initialHorizontalFirstAction_boundary hπ data D h1 hstart hk) q
  refine h.trans ?_
  change smoothHorizontalLaurentEvaluation D (τ * z) (L₁ _) = _
  rw [initialLineBoundaryMap]
  simp only [initialHorizontalFirstLineRestriction, AlgHom.comp_apply,
    AlgHom.restrictScalars_apply]
  have he := AlgHom.congr_fun
    (smoothHorizontalLaurentEvaluation_reciprocal D (τ * z) tangent⁻¹)
    (N₁ ((transition).symm (initialHorizontalBoundaryInput hπ data q)))
  rw [smoothHorizontalFirstLine_character] at he
  exact he

set_option maxRecDepth 2048 in
/-- The opposite actual action has the positive character with its negative reciprocal scale. -/
theorem initialHorizontalSecondAction_line :
    smoothHorizontalSecondAction (k := start) D d hstart (by omega) hπ =
      ((smoothHorizontalLaurentEvaluation D (τ * (j (-tangent)⁻¹ * z⁻¹))).restrictScalars R).comp
        (initialHorizontalSecondLineRestriction hπ data D h1 hstart hk) := by
  apply AlgHom.ext
  intro q
  have h := AlgHom.congr_fun (initialHorizontalSecondAction_boundary hπ data D h1 hstart hk) q
  refine h.trans ?_
  change smoothHorizontalLaurentEvaluation D (τ⁻¹ * z) (L₂ _) = _
  rw [initialLineBoundaryMap]
  simp only [initialHorizontalSecondLineRestriction, AlgHom.comp_apply,
    AlgHom.restrictScalars_apply]
  have he := AlgHom.congr_fun
    (smoothHorizontalLaurentEvaluation_reciprocal D (τ⁻¹ * z) (-tangent)⁻¹)
    (N₂ ((transition).symm (initialHorizontalBoundaryInput hπ data q)))
  rw [smoothHorizontalSecondLine_character] at he
  exact he

end FLT.Mazur.WeierstrassDividedDepth
