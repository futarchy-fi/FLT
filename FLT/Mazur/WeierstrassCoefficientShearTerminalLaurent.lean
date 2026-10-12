/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDilatationShearLaurentNormalForm
public import FLT.Mazur.WeierstrassCoefficientShearGluing
public import FLT.Mazur.PolygonCyclicCocone

/-!
# The whole nonsingular terminal Laurent chart in the coefficient model

The actual terminal equation with invertible divided constant is normalized
at an arbitrary tangent root, retaining its full image and coefficient map.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassDilatation
open scoped LaurentPolynomial
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option quotPrecheck false
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (S : Type u) [Field S] [Algebra R S] (r : S) (j : ℕ) (hj : j ≤ n)
local notation "d" => data (Fin.mk j (Nat.lt_succ_of_le hj))
variable (hs : algebraMap R S (π ^ (start + j)) = 0)
  (h3 : algebraMap R S (data ⟨j, Nat.lt_succ_of_le hj⟩).b3 = 0)
  (h4 : algebraMap R S (data ⟨j, Nat.lt_succ_of_le hj⟩).b4 = 0)
  (hc : IsUnit (algebraMap R S (data ⟨j, Nat.lt_succ_of_le hj⟩).b6))
  (hr : r ^ 2 + algebraMap R S W.a₁ * r - algebraMap R S W.a₂ = 0)
  (a : Sˣ) (ha : (a : S) = (rootShearCurve (W.map (algebraMap R S)) r).a₁)
local notation "e" => coefficientShearLaurentEquiv W (π ^ (start + j))
  (Data.b3 d) (Data.b4 d) (Data.b6 d) S r hs h3 h4 hr a ha hc
local notation "E" => Scheme.Spec.mapIso (e).toRingEquiv.toCommRingCatIso.op
local notation "G" => coefficientShearGluedIso hπ data S r j hj
local notation "base" => coefficientShearGluedStructure hπ data S r j hj

/-- The whole normalized terminal Laurent chart is an actual chart of the coefficient model. -/
def coefficientShearTerminalLaurent : Spec (.of (S[T;T⁻¹])) ⟶
    coefficientShearGlued hπ data S r j hj :=
  (E).hom ≫ coefficientShearGluedChart hπ data S r j hj (.inl 1)

local notation "N" => coefficientShearTerminalLaurent hπ data S r j hj hs h3 h4 hc hr a ha

instance coefficientShearTerminalLaurent_isOpenImmersion : IsOpenImmersion N :=
  inferInstanceAs (IsOpenImmersion (_ ≫ _))

/-- Reconstruction retains the entire original sheared divided equation. -/
@[reassoc] theorem coefficientShearTerminalLaurent_reconstruction :
    N ≫ (G).hom = (E).hom ≫ globalDividedCoefficientShearChart hπ data S r j hj := by
  rw [coefficientShearTerminalLaurent, Category.assoc, coefficientShearGluedIso_chart]
  rfl

/-- The full Laurent chart keeps the actual coefficient structure. -/
@[reassoc] theorem coefficientShearTerminalLaurent_structure :
    N ≫ base = (MultiplicativeGroupScheme.gm S).hom := by
  rw [coefficientShearTerminalLaurent, Category.assoc, coefficientShearGluedChart_structure]
  exact algebraSpecIso_structure e

end FLT.Mazur.WeierstrassDividedDepth
