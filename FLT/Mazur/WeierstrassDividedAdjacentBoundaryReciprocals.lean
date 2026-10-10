/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedFiniteLineReciprocals
public import FLT.Mazur.WeierstrassDividedFiniteLineBoundary

/-!
# Adjacent components agree on the entire preceding horizontal localization

The reciprocal comparison extends from the normalized node to every function
of the actual divided tensor algebra and its horizontal localization. This
uses the genuine parameter-corrected horizontal transition.
-/

@[expose] public noncomputable section
open IsLocalRing Polynomial
open scoped LaurentPolynomial
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

local notation "T" => WeierstrassDilatation.ScalarExtension W (π ^ (start + j + 1))
  (Data.b3 e) (Data.b4 e) (Data.b6 e) K
local notation "tx" => WeierstrassDilatation.tensorX W (π ^ (start + j + 1))
  (Data.b3 e) (Data.b4 e) (Data.b6 e) K
local notation "E" => WeierstrassDilatation.residuePolygonEquiv D (start + j + 1)
  (by omega) hk (Data.b3 e) (Data.b4 e) (Data.b6 e)
  (Data.factor3 e) (Data.factor4 e) (Data.factor6 e) (by omega)
local notation "cmap" => residueDividedConicMap D (start + j) hk
  (Data.b3 e) (Data.b4 e) (Data.b6 e) (Data.factor3 e) (Data.factor4 e)
local notation "l₁" => residueFiniteLineContraction hπ data D (j + 1) hjNext
  (by omega) hkNext 0 (by simp)
local notation "l₂" => residueFiniteLineContraction hπ data D (j + 1) hjNext
  (by omega) hkNext (-residue R W.a₁) (by simp)

/-- The first reciprocal comparison retains every function of the actual divided tensor chart. -/
theorem adjacentConicFirstLine_tensor (z : T) :
    g₁ (cmap z) = ρ₁ (Polynomial.toLaurent (l₁ z)) := by
  have H : ((g₁).comp cmap).comp (AlgEquiv.toAlgHom (AlgEquiv.symm E)) =
      ((ρ₁).comp (Polynomial.toLaurentAlg.comp l₁)).comp
        (AlgEquiv.toAlgHom (AlgEquiv.symm E)) := by
    have H₀ := adjacentConicFirstLine_algebra hπ data D j hj hk0 hk hjNext hkNext
    simp only [residueNodeConicMap, residueFiniteNodeLineMap, AlgHom.comp_assoc] at H₀ ⊢
    convert H₀ using 1
  exact AlgHom.congr_fun ((AlgHom.cancel_right (AlgEquiv.surjective (AlgEquiv.symm E))).mp H) z

/-- The opposite reciprocal comparison keeps the original negative tangent ordering. -/
theorem adjacentConicSecondLine_tensor (z : T) :
    g₂ (cmap z) = ρ₂ (Polynomial.toLaurent (l₂ z)) := by
  have H : ((g₂).comp cmap).comp (AlgEquiv.toAlgHom (AlgEquiv.symm E)) =
      ((ρ₂).comp (Polynomial.toLaurentAlg.comp l₂)).comp
        (AlgEquiv.toAlgHom (AlgEquiv.symm E)) := by
    have H₀ := adjacentConicSecondLine_algebra hπ data D j hj hk0 hk hjNext hkNext
    simp only [residueNodeConicMap, residueFiniteNodeLineMap, AlgHom.comp_assoc] at H₀ ⊢
    convert H₀ using 1
  exact AlgHom.congr_fun ((AlgHom.cancel_right (AlgEquiv.surjective (AlgEquiv.symm E))).mp H) z

local notation "copen" => residueDividedConicOpenEquiv D (start + j) hk
  (Data.b3 e) (Data.b4 e) (Data.b6 e) (Data.factor3 e) (Data.factor4 e)
local notation "b₁" => residueFiniteLineBoundaryMap hπ data D (j + 1) hjNext
  (by omega) hkNext 0 (by simp)
local notation "b₂" => residueFiniteLineBoundaryMap hπ data D (j + 1) hjNext
  (by omega) hkNext (-residue R W.a₁) (by simp)

/-- The full first conic boundary map equals the transported next line with reciprocal scale. -/
theorem adjacentConicFirstLine_localization :
    (g₁).comp (AlgEquiv.toAlgHom copen) = (ρ₁).comp b₁ := by
  apply IsLocalization.algHom_ext (Submonoid.powers tx)
  apply AlgHom.ext
  intro z
  change g₁ (cmap z) = ρ₁ (b₁ (algebraMap T _ z))
  exact (adjacentConicFirstLine_tensor hπ data D j hj hk0 hk hjNext hkNext z).trans
    (congrArg (ρ₁) (residueFiniteLineBoundaryMap_base hπ data D (j + 1)
      hjNext (by omega) hkNext 0 (by simp) z)).symm

/-- The entire opposite boundary map has the same equality with the negative reciprocal scale. -/
theorem adjacentConicSecondLine_localization :
    (g₂).comp (AlgEquiv.toAlgHom copen) = (ρ₂).comp b₂ := by
  apply IsLocalization.algHom_ext (Submonoid.powers tx)
  apply AlgHom.ext
  intro z
  change g₂ (cmap z) = ρ₂ (b₂ (algebraMap T _ z))
  exact (adjacentConicSecondLine_tensor hπ data D j hj hk0 hk hjNext hkNext z).trans
    (congrArg (ρ₂) (residueFiniteLineBoundaryMap_base hπ data D (j + 1)
      hjNext (by omega) hkNext (-residue R W.a₁) (by simp) z)).symm

end FLT.Mazur.WeierstrassDividedDepth
