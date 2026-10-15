/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSuccessiveNilpotentBranch
public import FLT.Mazur.QuadraticRootBranchChart

/-!
# Original polygon node opens in successive arithmetic Weierstrass charts

The slope is constructed from the original coefficients. Its simple-root
localization supplies an inverse, proving that the full polygon node chart
embeds as an open in the original successive chart over a nilpotent base.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassSuccessiveX
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) (s π b3 b4 b6 : R)
  (I : Ideal R) (hI : IsNilpotent I) (ha : IsUnit W.a₁) (hs : s ∈ I) (h2 : W.a₂ ∈ I)
  (h3 : b3 ∈ I) (h4 : b4 ∈ I) (h6 : b6 ∈ I)
local notation "v" => nilpotentNodeSlope W s π b3 b4 b6 I hI ha hs h2 h3 h4 h6
local notation "a" => nodeSlopeLinear W π b3
local notation "b" => nodeSlopeConstant W s π b4 b6
local notation "ev" => nilpotentNodeRetraction W s π b3 b4 b6 I hI ha hs h2 h3 h4 h6

/-- The constructed root has invertible separation from its opposite branch. -/
theorem nilpotentNodeSlope_simple : IsUnit (v + v + a) :=
  (NilpotentQuadraticRoot.element_nilpotent _ (nodeArithmeticIdeal_nilpotent π I hI)
    ((nodeArithmeticIdeal π I).add_mem
      (nilpotentNodeSlope_mem W s π b3 b4 b6 I hI ha hs h2 h3 h4 h6)
      (nilpotentNodeSlope_mem W s π b3 b4 b6 I hI ha hs h2 h3 h4 h6))).isUnit_add_right_of_commute
    (nodeSlopeLinear_unit W π b3 I hI ha h3) (mul_comm _ _)

/-- The simple-root evaluation of the monic model retains the original chart evaluation. -/
theorem nilpotentNodeRetraction_monic :
    ((QuadraticRootBranchLocalization.evaluation a b v
      (nilpotentNodeSlope_equation W s π b3 b4 b6 I hI ha hs h2 h3 h4 h6)).restrictScalars R).comp
        (toMonic W s π b3 b4 b6) = ev := by
  apply hom_ext
  intro i
  change QuadraticRootBranchLocalization.evaluation a b v
    (nilpotentNodeSlope_equation W s π b3 b4 b6 I hI ha hs h2 h3 h4 h6)
      (toMonic W s π b3 b4 b6 (coord W s π b3 b4 b6 i)) = ev (coord W s π b3 b4 b6 i)
  rw [toMonic_coord, nilpotentNodeRetraction_coord]
  fin_cases i
  · exact (QuadraticRootBranchLocalization.evaluation a b v
      (nilpotentNodeSlope_equation W s π b3 b4 b6 I hI ha hs h2 h3 h4 h6)).commutes _
  · exact QuadraticRootBranchLocalization.evaluation_root a b v _
  · exact (QuadraticRootBranchLocalization.evaluation a b v
      (nilpotentNodeSlope_equation W s π b3 b4 b6 I hI ha hs h2 h3 h4 h6)).commutes _

/-- The actual node section in the original three-coordinate spectrum. -/
def nilpotentNodeChart : Spec (.of (SuccessiveIncidence.Coordinate π)) ⟶
    Spec (.of (Coordinate W s π b3 b4 b6)) :=
  Spec.map (CommRingCat.ofHom (ev).toRingHom)

/-- The constructed original branch is an open immersion with the localization inverse. -/
theorem nilpotentNodeChart_isOpenImmersion :
    IsOpenImmersion (nilpotentNodeChart W s π b3 b4 b6 I hI ha hs h2 h3 h4 h6) := by
  have he := nilpotentNodeRetraction_monic W s π b3 b4 b6 I hI ha hs h2 h3 h4 h6
  unfold nilpotentNodeChart
  rw [← he]
  simp only [AlgHom.toRingHom_eq_coe, AlgHom.comp_toRingHom, CommRingCat.ofHom_comp,
    Spec.map_comp]
  have hm : IsIso (CommRingCat.ofHom (toMonic W s π b3 b4 b6).toRingHom) :=
    (monicEquiv W s π b3 b4 b6).toRingEquiv.toCommRingCatIso.isIso_hom
  have hb := QuadraticRootBranchLocalization.branchChart_isOpenImmersion a b v
    (nilpotentNodeSlope_equation W s π b3 b4 b6 I hI ha hs h2 h3 h4 h6)
    (nilpotentNodeSlope_simple W s π b3 b4 b6 I hI ha hs h2 h3 h4 h6)
  change IsOpenImmersion (QuadraticRootBranchLocalization.branchChart a b v
    (nilpotentNodeSlope_equation W s π b3 b4 b6 I hI ha hs h2 h3 h4 h6) ≫
      Spec.map (CommRingCat.ofHom (toMonic W s π b3 b4 b6).toRingHom))
  exact IsOpenImmersion.comp _ _

/-- The same constructed branch with the actual polygon node ring as source. -/
def nilpotentPolygonChart : Spec (.of (PolygonSmoothing.ChartRing π)) ⟶
    Spec (.of (Coordinate W s π b3 b4 b6)) :=
  Spec.map (CommRingCat.ofHom (SuccessiveIncidence.toPolygon π).toRingHom) ≫
    nilpotentNodeChart W s π b3 b4 b6 I hI ha hs h2 h3 h4 h6

/-- The coefficient-preserving polygon chart is an actual open in the original model. -/
theorem nilpotentPolygonChart_isOpenImmersion :
    IsOpenImmersion (nilpotentPolygonChart W s π b3 b4 b6 I hI ha hs h2 h3 h4 h6) := by
  have he : IsIso (CommRingCat.ofHom (SuccessiveIncidence.toPolygon π).toRingHom) :=
    (SuccessiveIncidence.polygonEquiv π).toRingEquiv.toCommRingCatIso.isIso_hom
  have hn := nilpotentNodeChart_isOpenImmersion W s π b3 b4 b6 I hI ha hs h2 h3 h4 h6
  exact IsOpenImmersion.comp _ _

/-- The node chart keeps the unchanged original coefficient morphism. -/
@[reassoc] theorem nilpotentPolygonChart_structure :
    nilpotentPolygonChart W s π b3 b4 b6 I hI ha hs h2 h3 h4 h6 ≫
      Spec.map (CommRingCat.ofHom (algebraMap R (Coordinate W s π b3 b4 b6))) =
      Spec.map (CommRingCat.ofHom (algebraMap R (PolygonSmoothing.ChartRing π))) := by
  simp only [nilpotentPolygonChart, nilpotentNodeChart, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  ext x
  exact ((SuccessiveIncidence.toPolygon π).comp ev).commutes x

end FLT.Mazur.WeierstrassSuccessiveX
