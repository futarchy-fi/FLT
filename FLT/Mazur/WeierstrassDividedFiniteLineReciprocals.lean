/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedFiniteLineBranches
public import FLT.Mazur.WeierstrassSuccessiveXTerminalConicBranches
public import FLT.Mazur.PolygonScaledReciprocal

/-!
# Ordered scaled reciprocal transitions between adjacent residue components

Both comparisons are identities on the complete preceding node algebra.
The first conic puncture meets the next zero-slope line with U = a₁⁻¹/Z;
the second meets the opposite line with U = -a₁⁻¹/Z.
-/

@[expose] public noncomputable section
open IsLocalRing Polynomial
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type*} [CommRing R] [IsDomain R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (D : SplitNodeDepth W π depth) (j : ℕ) (hj : j + 1 ≤ n)
  (hk0 : 0 < start + j) (hk : 2 * (start + j + 1) ≤ depth)
local notation "K" => ResidueField R
local notation "a" => WeierstrassDilatation.residueTangentUnit D
local notation "f₁" => residueFiniteNodeLineMap hπ data D j hj hk0 hk 0 (by simp)
local notation "f₂" => residueFiniteNodeLineMap hπ data D j hj hk0 hk
  (-residue R W.a₁) (by simp)
local notation "ρ₁" => PolygonScaledReciprocal.reciprocal (a)⁻¹
local notation "ρ₂" => PolygonScaledReciprocal.reciprocal (-a)⁻¹

/-- The first horizontal parameter meets the reciprocal right node coordinate. -/
theorem residueFiniteFirstLine_reciprocal :
    (ρ₁).comp (Polynomial.toLaurentAlg.comp f₁) =
      LaurentPolynomial.invert.toAlgHom.comp
        (Polynomial.toLaurentAlg.comp PolygonNodeEqualizer.second) := by
  rw [residueFiniteNodeFirstLine_eq,
    ← WeierstrassDilatation.residueTangentUnit_val D, ← AlgHom.comp_assoc Polynomial.toLaurentAlg,
    ← AlgHom.comp_assoc, PolygonScaledReciprocal.reciprocal_scaled_affine, AlgHom.comp_assoc]

/-- The opposite horizontal parameter keeps the negative reciprocal scale. -/
theorem residueFiniteSecondLine_reciprocal :
    (ρ₂).comp (Polynomial.toLaurentAlg.comp f₂) =
      LaurentPolynomial.invert.toAlgHom.comp
        (Polynomial.toLaurentAlg.comp PolygonNodeEqualizer.first) := by
  rw [residueFiniteNodeSecondLine_eq,
    ← WeierstrassDilatation.residueTangentUnit_val D]
  change (PolygonScaledReciprocal.reciprocal (-a)⁻¹).comp
    (Polynomial.toLaurentAlg.comp
      ((aeval (C (↑(-a) : K) * X)).comp PolygonNodeEqualizer.first)) = _
  rw [← AlgHom.comp_assoc Polynomial.toLaurentAlg, ← AlgHom.comp_assoc,
    PolygonScaledReciprocal.reciprocal_scaled_affine, AlgHom.comp_assoc]

variable (hjNext : j + 2 ≤ n) (hkNext : 2 * (start + (j + 1) + 1) ≤ depth)
open WeierstrassSuccessiveX
local notation "e" => data (Fin.mk (j + 1) (Nat.lt_succ_of_le hj))
local notation "W₀" => W.map (residue R)
local notation "c" => residue R (Data.b6 e)
local notation "ha" => D.a₁_unit.map (residue R)
local notation "hc" => Iff.mpr (residue_eq_zero_iff _)
  (WeierstrassDilatation.divided_constant_mem D (start + j + 1) (by omega)
    (Data.b6 e) (Data.factor6 e))
local notation "ψ" => residueNodeConicMap D (start + j) hk
  (Data.b3 e) (Data.b4 e) (Data.b6 e) (Data.factor3 e) (Data.factor4 e) (Data.factor6 e) (by omega)
local notation "g₁" => conicBoundaryFirst W₀ c ha hc
local notation "g₂" => conicBoundarySecond W₀ c ha hc
local notation "N₁" => residueFiniteNodeLineMap hπ data D (j + 1) hjNext
  (by omega) hkNext 0 (by simp)
local notation "N₂" => residueFiniteNodeLineMap hπ data D (j + 1) hjNext
  (by omega) hkNext (-residue R W.a₁) (by simp)

/-- The first original conic puncture equals the next line after scaled reciprocal transport. -/
theorem adjacentConicFirstLine_algebra :
    (g₁).comp ψ = (ρ₁).comp (Polynomial.toLaurentAlg.comp N₁) := by
  rw [residueNodeConicFirst_eq, residueFiniteFirstLine_reciprocal]

/-- The second original conic puncture meets the opposite line with the negative scale. -/
theorem adjacentConicSecondLine_algebra :
    (g₂).comp ψ = (ρ₂).comp (Polynomial.toLaurentAlg.comp N₂) := by
  rw [residueNodeConicSecond_eq, residueFiniteSecondLine_reciprocal]

open AlgebraicGeometry CategoryTheory
open scoped LaurentPolynomial

universe v

/-- Spectrum reverses composition without unfolding the concrete algebra maps. -/
theorem lineSpec_comp {S₀ A B C : Type v} [CommRing S₀] [CommRing A] [CommRing B]
    [CommRing C] [Algebra S₀ A] [Algebra S₀ B] [Algebra S₀ C]
    (f : A →ₐ[S₀] B) (g : B →ₐ[S₀] C) :
    Spec.map (CommRingCat.ofHom (g.comp f).toRingHom) =
      Spec.map (CommRingCat.ofHom g.toRingHom) ≫
        Spec.map (CommRingCat.ofHom f.toRingHom) := by
  rw [← Spec.map_comp]
  rfl

/-- The first puncture and the next line give the same actual map to the preceding node. -/
theorem adjacentConicFirstLine_spec :
    Spec.map (CommRingCat.ofHom (AlgHom.toRingHom g₁)) ≫
      Spec.map (CommRingCat.ofHom (AlgHom.toRingHom ψ)) =
        Spec.map (CommRingCat.ofHom (AlgHom.toRingHom ρ₁)) ≫
          Spec.map (CommRingCat.ofHom Polynomial.toLaurent) ≫
            Spec.map (CommRingCat.ofHom (AlgHom.toRingHom N₁)) := by
  rw [← lineSpec_comp ψ g₁]
  have H := adjacentConicFirstLine_algebra hπ data D j hj hk0 hk hjNext hkNext
  rw [H, lineSpec_comp, lineSpec_comp]
  rfl

/-- The opposite puncture gives the other ordered node map with its negative scale. -/
theorem adjacentConicSecondLine_spec :
    Spec.map (CommRingCat.ofHom (AlgHom.toRingHom g₂)) ≫
      Spec.map (CommRingCat.ofHom (AlgHom.toRingHom ψ)) =
        Spec.map (CommRingCat.ofHom (AlgHom.toRingHom ρ₂)) ≫
          Spec.map (CommRingCat.ofHom Polynomial.toLaurent) ≫
            Spec.map (CommRingCat.ofHom (AlgHom.toRingHom N₂)) := by
  rw [← lineSpec_comp ψ g₂]
  have H := adjacentConicSecondLine_algebra hπ data D j hj hk0 hk hjNext hkNext
  rw [H, lineSpec_comp, lineSpec_comp]
  rfl

end FLT.Mazur.WeierstrassDividedDepth
