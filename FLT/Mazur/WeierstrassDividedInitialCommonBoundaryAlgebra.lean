/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedFiniteLineReciprocals
public import FLT.Mazur.WeierstrassDividedFiniteLineBoundary

/-!
# The original initial common boundary has both signed reciprocal line maps

The reciprocal comparison extends from the normalized node to every function
of the actual divided tensor algebra and its horizontal localization. This
uses the genuine parameter-corrected horizontal transition at the initial stage.
-/

@[expose] public noncomputable section
open IsLocalRing Polynomial
open scoped LaurentPolynomial
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type*} [CommRing R] [IsDomain R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {k n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (k + 1 + i.val))
  (D : SplitNodeDepth W π depth) (h1 : 1 ≤ n) (hk : 2 * (k + 2) ≤ depth)
open WeierstrassSuccessiveX
local notation "K" => ResidueField R
local notation "a" => WeierstrassDilatation.residueTangentUnit D
local notation "e" => data (Fin.mk 0 (Nat.zero_lt_succ n))
local notation "W₀" => W.map (residue R)
local notation "c" => residue R (Data.b6 e)
local notation "ha" => D.a₁_unit.map (residue R)
local notation "hc" => Iff.mpr (residue_eq_zero_iff _)
  (WeierstrassDilatation.divided_constant_mem D (k + 1) (by omega)
    (Data.b6 e) (Data.factor6 e))
local notation "ρ₁" => PolygonScaledReciprocal.reciprocal (a)⁻¹
local notation "ρ₂" => PolygonScaledReciprocal.reciprocal (-a)⁻¹
local notation "ψ" => residueNodeConicMap D k (by omega)
  (Data.b3 e) (Data.b4 e) (Data.b6 e) (Data.factor3 e) (Data.factor4 e) (Data.factor6 e) (by omega)
local notation "g₁" => conicBoundaryFirst W₀ c ha hc
local notation "g₂" => conicBoundarySecond W₀ c ha hc
local notation "N₁" => residueFiniteNodeLineMap hπ data D 0 h1
  (by omega) (by omega) 0 (by simp)
local notation "N₂" => residueFiniteNodeLineMap hπ data D 0 h1
  (by omega) (by omega) (-residue R W.a₁) (by simp)
local notation "T" => WeierstrassDilatation.ScalarExtension W (π ^ (k + 1))
  (Data.b3 e) (Data.b4 e) (Data.b6 e) K
local notation "tx" => WeierstrassDilatation.tensorX W (π ^ (k + 1))
  (Data.b3 e) (Data.b4 e) (Data.b6 e) K
local notation "E" => WeierstrassDilatation.residuePolygonEquiv D (k + 1)
  (by omega) (by omega) (Data.b3 e) (Data.b4 e) (Data.b6 e)
  (Data.factor3 e) (Data.factor4 e) (Data.factor6 e) (by omega)
local notation "cmap" => residueDividedConicMap D k (by omega)
  (Data.b3 e) (Data.b4 e) (Data.b6 e) (Data.factor3 e) (Data.factor4 e)
local notation "l₁" => residueFiniteLineContraction hπ data D 0 h1
  (by omega) (by omega) 0 (by simp)
local notation "l₂" => residueFiniteLineContraction hπ data D 0 h1
  (by omega) (by omega) (-residue R W.a₁) (by simp)

/-- The initial positive puncture retains the original reciprocal line normalization. -/
theorem initialCommonFirstLine_algebra :
    (g₁).comp ψ = (ρ₁).comp (Polynomial.toLaurentAlg.comp N₁) := by
  rw [residueNodeConicFirst_eq, residueFiniteFirstLine_reciprocal]

/-- The initial opposite puncture retains the original negative reciprocal scale. -/
theorem initialCommonSecondLine_algebra :
    (g₂).comp ψ = (ρ₂).comp (Polynomial.toLaurentAlg.comp N₂) := by
  rw [residueNodeConicSecond_eq, residueFiniteSecondLine_reciprocal]

/-- The first reciprocal comparison retains every function of the actual divided tensor chart. -/
theorem initialCommonFirstLine_tensor (z : T) :
    g₁ (cmap z) = ρ₁ (Polynomial.toLaurent (l₁ z)) := by
  have H : ((g₁).comp cmap).comp (AlgEquiv.toAlgHom (AlgEquiv.symm E)) =
      ((ρ₁).comp (Polynomial.toLaurentAlg.comp l₁)).comp
        (AlgEquiv.toAlgHom (AlgEquiv.symm E)) := by
    have H₀ := initialCommonFirstLine_algebra hπ data D h1 hk
    simp only [residueNodeConicMap, residueFiniteNodeLineMap, AlgHom.comp_assoc] at H₀ ⊢
    convert H₀ using 1
  exact AlgHom.congr_fun ((AlgHom.cancel_right (AlgEquiv.surjective (AlgEquiv.symm E))).mp H) z

/-- The opposite reciprocal comparison keeps the original negative tangent ordering. -/
theorem initialCommonSecondLine_tensor (z : T) :
    g₂ (cmap z) = ρ₂ (Polynomial.toLaurent (l₂ z)) := by
  have H : ((g₂).comp cmap).comp (AlgEquiv.toAlgHom (AlgEquiv.symm E)) =
      ((ρ₂).comp (Polynomial.toLaurentAlg.comp l₂)).comp
        (AlgEquiv.toAlgHom (AlgEquiv.symm E)) := by
    have H₀ := initialCommonSecondLine_algebra hπ data D h1 hk
    simp only [residueNodeConicMap, residueFiniteNodeLineMap, AlgHom.comp_assoc] at H₀ ⊢
    convert H₀ using 1
  exact AlgHom.congr_fun ((AlgHom.cancel_right (AlgEquiv.surjective (AlgEquiv.symm E))).mp H) z

local notation "copen" => residueDividedConicOpenEquiv D k (by omega)
  (Data.b3 e) (Data.b4 e) (Data.b6 e) (Data.factor3 e) (Data.factor4 e)
local notation "b₁" => residueFiniteLineBoundaryMap hπ data D 0 h1
  (by omega) (by omega) 0 (by simp)
local notation "b₂" => residueFiniteLineBoundaryMap hπ data D 0 h1
  (by omega) (by omega) (-residue R W.a₁) (by simp)

/-- The full first conic boundary map equals the transported next line with reciprocal scale. -/
theorem initialCommonFirstLine_localization :
    (g₁).comp (AlgEquiv.toAlgHom copen) = (ρ₁).comp b₁ := by
  apply IsLocalization.algHom_ext (Submonoid.powers tx)
  apply AlgHom.ext
  intro z
  change g₁ (cmap z) = ρ₁ (b₁ (algebraMap T _ z))
  exact (initialCommonFirstLine_tensor hπ data D h1 hk z).trans
    (congrArg (ρ₁) (residueFiniteLineBoundaryMap_base hπ data D 0
      h1 (by omega) (by omega) 0 (by simp) z)).symm

/-- The entire opposite boundary map has the same equality with the negative reciprocal scale. -/
theorem initialCommonSecondLine_localization :
    (g₂).comp (AlgEquiv.toAlgHom copen) = (ρ₂).comp b₂ := by
  apply IsLocalization.algHom_ext (Submonoid.powers tx)
  apply AlgHom.ext
  intro z
  change g₂ (cmap z) = ρ₂ (b₂ (algebraMap T _ z))
  exact (initialCommonSecondLine_tensor hπ data D h1 hk z).trans
    (congrArg (ρ₂) (residueFiniteLineBoundaryMap_base hπ data D 0
      h1 (by omega) (by omega) (-residue R W.a₁) (by simp) z)).symm

end FLT.Mazur.WeierstrassDividedDepth
