/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticTerminalCyclicCoordinates
public import FLT.Mazur.EllipticMiddleCyclicCoordinates
public import FLT.Mazur.EllipticNodeTrivializedIndexTransport
public import FLT.Mazur.EllipticResolvedOrientedAtlas

/-!
# Natural terminal labels in the original cyclic normalization

The actual oriented smooth atlas has the same terminal labels as the complete
cyclic normalization, with the explicitly calculated arithmetic scales.
Only equality of stage indices is used to compare the original targets.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {K : Type u} [Field K] (A : ValuationSubring K)
  {W : WeierstrassCurve A} {π : A} {depth : ℕ} (D : SplitNodeDepth W π depth)
  (r : (ResidueField A)ˣ)
local notation "F" => ResidueField A
local notation "hπ" => SplitNodeDepth.uniformizer_ne_zero D
local notation "data" => splitResolutionData A D
local notation "p" => resolvedSplitStructure A D
local notation "e" => resolvedComponentIndexEquiv D.depth_pos

/-- The natural positive terminal label retains the actual original arithmetic chart. -/
@[reassoc] theorem resolvedOrientedComponentChart_terminalPositive
    (hk0 : 0 < depth / 2) (hp : 2 * (depth / 2) < depth) :
    resolvedOrientedComponentChart A D r ⟨depth / 2, by omega⟩ ≫ (p).smoothLocus.ι =
      resolvedTerminalPositiveChart A D r hk0 hp := by
  have hi : (e) (.terminalPositive hk0 hp) = ⟨depth / 2, by omega⟩ := rfl
  rw [← hi, resolvedOrientedComponentChart, Equiv.symm_apply_apply]
  simp only [resolvedComponentOrientation, reduceCtorEq, ite_false, Iso.refl_hom,
    Category.id_comp, resolvedComponentChart, resolvedTerminalPositiveSmoothChart_inclusion]

/-- The complementary terminal label retains the actual negative arithmetic chart. -/
@[reassoc] theorem resolvedOrientedComponentChart_terminalNegative
    (hk0 : 0 < depth / 2) (hp : 2 * (depth / 2) < depth) :
    resolvedOrientedComponentChart A D r ⟨depth - depth / 2, by omega⟩ ≫
        (p).smoothLocus.ι = resolvedTerminalNegativeChart A D r hk0 hp := by
  have hi : (e) (.terminalNegative hk0 hp) = ⟨depth - depth / 2, by omega⟩ := rfl
  rw [← hi, resolvedOrientedComponentChart, Equiv.symm_apply_apply]
  simp only [resolvedComponentOrientation, reduceCtorEq, ite_false, Iso.refl_hom,
    Category.id_comp, resolvedComponentChart, resolvedTerminalNegativeSmoothChart_inclusion]

/-- The unique even midpoint label retains the original middle arithmetic chart. -/
@[reassoc] theorem resolvedOrientedComponentChart_terminalMiddle
    (hk0 : 0 < depth / 2) (hp : 2 * (depth / 2) = depth) :
    resolvedOrientedComponentChart A D r ⟨depth / 2, by omega⟩ ≫ (p).smoothLocus.ι =
      resolvedTerminalMiddleChart A D r hk0 hp := by
  have hi : (e) (.terminalMiddle hk0 hp) = ⟨depth / 2, by omega⟩ := rfl
  rw [← hi, resolvedOrientedComponentChart, Equiv.symm_apply_apply]
  simp only [resolvedComponentOrientation, reduceCtorEq, ite_false, Iso.refl_hom,
    Category.id_comp, resolvedComponentChart, resolvedTerminalMiddleSmoothChart_inclusion]

variable (s : ℕ) (he : depth / 2 = s + 1)
local notation "t" => eqToHom (finiteGlobalTensorModel_index_congr hπ data F
  (le_refl _) (by omega) he)
local notation "a" => nodeLaurentScale D r (0 + (s + 1))

/-- The positive W308 chart in the original complete odd cyclic normalization coordinates. -/
@[reassoc] theorem resolvedOrientedComponentChart_oddPositive_cyclic
    (hp : 2 * (s + 1) < depth) :
    resolvedOrientedComponentChart A D r ⟨depth / 2, by omega⟩ ≫ (p).smoothLocus.ι ≫ t =
      Spec.map (CommRingCat.ofHom (PolygonScaledReciprocal.scaling a).toRingHom) ≫
        (PolygonPinching.torusToComponent F).left ≫
          (zeroSplitCycleComponent hπ data D s (by omega) rfl (by omega) (by omega)
            ⟨s + 1, by omega⟩).left := by
  rw [resolvedOrientedComponentChart_terminalPositive_assoc A D r (by omega) (by omega)]
  change nodeTrivializedPositiveChart A hπ data D r _ _ _ _ ≫ t = _
  rw [nodeTrivializedPositiveChart_index_transport A hπ data D r
    (le_refl _) (by omega) he (by omega) (by omega)]
  exact nodeTrivializedPositiveChart_cyclic A hπ data D r s (by omega) rfl (by omega)

/-- The negative W308 chart in the original complete odd cyclic normalization coordinates. -/
@[reassoc] theorem resolvedOrientedComponentChart_oddNegative_cyclic
    (hp : 2 * (s + 1) < depth) :
    resolvedOrientedComponentChart A D r ⟨depth - depth / 2, by omega⟩ ≫
        (p).smoothLocus.ι ≫ t =
      Spec.map (CommRingCat.ofHom (PolygonScaledReciprocal.scaling (-a)⁻¹).toRingHom) ≫
        (PolygonPinching.torusToComponent F).left ≫
          (zeroSplitCycleComponent hπ data D s (by omega) rfl (by omega) (by omega)
            ⟨s + 2, by omega⟩).left := by
  rw [resolvedOrientedComponentChart_terminalNegative_assoc A D r (by omega) (by omega)]
  change nodeTrivializedNegativeChart A hπ data D r _ _ _ _ ≫ t = _
  rw [nodeTrivializedNegativeChart_index_transport A hπ data D r
    (le_refl _) (by omega) he (by omega) (by omega)]
  exact nodeTrivializedNegativeChart_cyclic A hπ data D r s (by omega) rfl (by omega)

/-- The even midpoint W308 chart in the original complete cyclic normalization coordinates. -/
@[reassoc] theorem resolvedOrientedComponentChart_evenMiddle_cyclic
    (hp : 2 * (s + 1) = depth) :
    resolvedOrientedComponentChart A D r ⟨depth / 2, by omega⟩ ≫ (p).smoothLocus.ι ≫ t =
      Spec.map (CommRingCat.ofHom (PolygonScaledReciprocal.scaling (-a)⁻¹).toRingHom) ≫
        (PolygonPinching.torusToComponent F).left ≫
          (zeroEqualityCycleComponent hπ data D s (by omega) rfl (by omega) (by omega)
            ⟨s + 1, by omega⟩).left := by
  rw [resolvedOrientedComponentChart_terminalMiddle_assoc A D r (by omega) (by omega)]
  change nodeTrivializedMiddleChart A hπ data D r _ _ _ _ ≫ t = _
  rw [nodeTrivializedMiddleChart_index_transport A hπ data D r
    (le_refl _) (by omega) he (by omega) (by omega)]
  exact nodeTrivializedMiddleChart_cyclic A hπ data D s (by omega) rfl (by omega) r

end FLT.Mazur.WeierstrassDividedDepth
