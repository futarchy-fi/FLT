/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.ProjectiveLineValuationExtension
public import FLT.Mazur.WeierstrassDividedFiniteOriginalXOpen

/-!
# Lifting a complete normalization to the original finite model

The unchanged original D(x) constructs the lift on a dense open. Properness
extends it across both node preimages and infinity. The regular original x
coordinate proves uniqueness of the lift to the actual finite modification.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassIntegralChart ProjectiveLine
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val)) (j : ℕ) (hj : j ≤ n)
  {K : Type u} [Field K] (φ : Coordinate W 2 →+* Polynomial K)
  (hx : IsRegular (φ (coord W 2 0)))
  (q : scheme K ⟶ integralCurve W)
  (hq : left K ≫ q = Spec.map (CommRingCat.ofHom φ) ≫ integralCurveChart W 2)
local notation "c" => finiteGlobalContraction hπ data j hj
local notation "x" => coord W 2 0
local notation "U" => Localization.Away (φ x)
local notation "i" => PrincipalAffineRefinement.inclusion (φ x)
local notation "e" => finiteOriginalXOpen hπ data j hj ≫ finiteLocalChart hπ data j hj

/-- The original D(x) map, constructed using the actual inverse finite contraction. -/
def projectiveFiniteLiftOpen : Spec (.of U) ⟶ finiteGlobalModel hπ data j hj :=
  Spec.map (CommRingCat.ofHom
    (IsLocalization.Away.map (S := Localization.Away x) (Q := U) φ x)) ≫ e

include hq in
/-- The open lift has exactly the original unsheared cubic projection. -/
@[reassoc] theorem projectiveFiniteLiftOpen_contraction :
    projectiveFiniteLiftOpen hπ data j hj φ ≫ c = i ≫ left K ≫ q := by
  rw [projectiveFiniteLiftOpen, Category.assoc]
  have hc := (finiteOriginalXOpen_isPullback hπ data j hj).w
  simp only [Category.id_comp] at hc
  rw [← hc, RegularPrincipalOpen.map_inclusion_assoc, hq]

include hx hq in
/-- Every complete normalization with regular original x lifts to the actual finite model. -/
theorem exists_projectiveFiniteLift :
    ∃ f : scheme K ⟶ finiteGlobalModel hπ data j hj, f ≫ c = q := by
  let _ := finiteGlobalContraction_isProper hπ data j hj
  let _ := RegularPrincipalOpen.inclusion_schematicallyDense (φ x) hx
  obtain ⟨f, hf, _⟩ := exists_openImmersion_extension_of_valuation_stalks
    q c (i ≫ left K) (projectiveFiniteLiftOpen hπ data j hj φ)
    (by simpa only [Category.assoc] using
      projectiveFiniteLiftOpen_contraction hπ data j hj φ q hq)
  exact ⟨f, hf⟩

include hx hq in
/-- The original unchanged open detects all complete lifts, including over the two node points. -/
theorem projectiveFiniteLift_unique
    (f g : scheme K ⟶ finiteGlobalModel hπ data j hj)
    (hf : f ≫ c = q) (hg : g ≫ c = q) : f = g := by
  let _ := finiteGlobalContraction_isProper hπ data j hj
  refine ext_of_isDominant_of_isSeparated c (hf.trans hg.symm) (left K) ?_
  exact finiteGlobalContraction_ext_of_regular_x hπ data j hj φ hx _ _
    (by rw [Category.assoc, hf, hq]) (by rw [Category.assoc, hg, hq])

/-- The complete lift is constructed, rather than supplied as a descent hypothesis. -/
def projectiveFiniteLift : scheme K ⟶ finiteGlobalModel hπ data j hj :=
  (exists_projectiveFiniteLift hπ data j hj φ hx q hq).choose

/-- All original cubic functions are retained by the constructed complete lift. -/
@[reassoc] theorem projectiveFiniteLift_contraction :
    projectiveFiniteLift hπ data j hj φ hx q hq ≫ c = q :=
  (exists_projectiveFiniteLift hπ data j hj φ hx q hq).choose_spec

end FLT.Mazur.WeierstrassDividedDepth
