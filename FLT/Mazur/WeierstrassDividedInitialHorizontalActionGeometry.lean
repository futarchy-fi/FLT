/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedInitialHorizontalLineAction
public import FLT.Mazur.WeierstrassDividedFiniteLineBoundaryGeometry

/-!
# The initial horizontal action through the original geometric line boundary

Taking spectra retains the original next-line lift and both tensor transitions.
The source still has conic factor first and smooth factor second.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory IsLocalRing
open scoped LaurentPolynomial
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
local notation "e" => data (Fin.mk 1 (Nat.lt_succ_of_le h1))
local notation "a" => residue R W.a₁
local notation "tangent" => WeierstrassDilatation.residueTangentUnit D
local notation "t₀" => WeierstrassModificationX.t W (π ^ start)
  (Data.b3 d) (Data.b4 d) (Data.b6 d)
local notation "x₀" => WeierstrassDilatation.x W (π ^ start)
  (Data.b3 d) (Data.b4 d) (Data.b6 d)
local notation "u₀" => coord W (π ^ start) π (Data.b3 e) (Data.b4 e) (Data.b6 e) 2
local notation "A" => PrincipalOpenTensor.transitionIso K x₀ t₀
  (overlapEquiv W (π ^ start) (Data.b3 d) (Data.b4 d) (Data.b6 d))
local notation "B" => PrincipalOpenTensor.transitionIso K x₀ u₀ (previousBoundaryEquiv hπ d e)
local notation "L" => residueLineToHorizontal D start hstart hk
  (Data.b3 e) (Data.b4 e) (Data.b6 e) (Data.factor3 e) (Data.factor4 e)
local notation "p" => Spec.map (CommRingCat.ofHom
  (AlgHom.toRingHom (initialHorizontalBoundaryInput hπ data)))
local notation "τ" => smoothHorizontalTangentUnit D
local notation "z" => smoothHorizontalConicUnit D
local notation "C" => SmoothHorizontalResidueRing D
local notation "j" => Units.map (algebraMap K C)

/-- The original first-line restriction is its actual geometric boundary and transition. -/
theorem initialHorizontalFirstLineRestriction_spec :
    Spec.map (CommRingCat.ofHom
      (initialHorizontalFirstLineRestriction hπ data D h1 hstart hk).toRingHom) =
      L 0 (by simp) ≫ (B).hom ≫ (A).inv ≫ p := by
  rw [initialHorizontalFirstLineRestriction, lineSpec_comp, lineSpec_comp]
  have h := residueFiniteLineBoundary_spec hπ data D 0 h1 hstart hk 0 (by simp)
  have H := congrArg (fun f => f ≫ (A).inv ≫ p) h.symm
  simp only [Category.assoc] at H
  exact H

/-- The opposite line retains the same boundary geometry with the negative tangent slope. -/
theorem initialHorizontalSecondLineRestriction_spec :
    Spec.map (CommRingCat.ofHom
      (initialHorizontalSecondLineRestriction hπ data D h1 hstart hk).toRingHom) =
      L (-a) (by simp) ≫ (B).hom ≫ (A).inv ≫ p := by
  rw [initialHorizontalSecondLineRestriction, lineSpec_comp, lineSpec_comp]
  have h := residueFiniteLineBoundary_spec hπ data D 0 h1 hstart hk (-a) (by simp)
  have H := congrArg (fun f => f ≫ (A).inv ≫ p) h.symm
  simp only [Category.assoc] at H
  exact H

/-- The first actual action factors through the retained geometric next-line lift. -/
theorem initialHorizontalFirstAction_boundary_spec :
    Spec.map (CommRingCat.ofHom
      (smoothHorizontalFirstAction (k := start) D d hstart (by omega) hπ).toRingHom) =
    Spec.map (CommRingCat.ofHom
      (smoothHorizontalLaurentEvaluation D (τ⁻¹ * (j tangent⁻¹ * z⁻¹))).toRingHom) ≫
      L 0 (by simp) ≫ (B).hom ≫ (A).inv ≫ p := by
  rw [initialHorizontalFirstAction_line hπ data D h1 hstart hk, lineSpec_comp]
  rw [initialHorizontalFirstLineRestriction_spec]
  rfl

/-- The opposite actual action retains its signed reciprocal coordinate and geometric lift. -/
theorem initialHorizontalSecondAction_boundary_spec :
    Spec.map (CommRingCat.ofHom
      (smoothHorizontalSecondAction (k := start) D d hstart (by omega) hπ).toRingHom) =
    Spec.map (CommRingCat.ofHom
      (smoothHorizontalLaurentEvaluation D (τ * (j (-tangent)⁻¹ * z⁻¹))).toRingHom) ≫
      L (-a) (by simp) ≫ (B).hom ≫ (A).inv ≫ p := by
  rw [initialHorizontalSecondAction_line hπ data D h1 hstart hk, lineSpec_comp]
  rw [initialHorizontalSecondLineRestriction_spec]
  rfl

end FLT.Mazur.WeierstrassDividedDepth
