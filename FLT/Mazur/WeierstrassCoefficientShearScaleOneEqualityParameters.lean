/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientShearScaleOneEqualityComponent
public import FLT.Mazur.WeierstrassCoefficientShearEqualityChartParameters
import all FLT.Mazur.WeierstrassCoefficientShearRetainedScaleOneConic

/-!
# Original conic and divided parameters at scale-one equality

Extract the full chart maps from the already constructed completed component.
Both original conic markings and its nonzero constant are retained.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassSuccessiveX WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option quotPrecheck false
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (S : Type u) [Field S] [Algebra R S] (r : S) (j : ℕ) (hj : j + 1 ≤ n)
local notation "d" => data (Fin.mk (j + 1) (Nat.lt_succ_of_le hj))
variable (hs : algebraMap R S (π ^ (start + j)) = 1) (hp : algebraMap R S π = 0)
  (h3 : algebraMap R S (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b3 = 0)
  (h4 : algebraMap R S (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b4 = 0)
  (hc : IsUnit (algebraMap R S (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b6))
  (hr : r ^ 2 + algebraMap R S W.a₁ * r - algebraMap R S W.a₂ = 0)
  (a : Sˣ) (ha : (a : S) = (rootShearCurve (W.map (algebraMap R S)) r).a₁)
local notation "U" => rootShearCurve (W.map (algebraMap R S)) r
local notation "c" => algebraMap R S (Data.b6 d)
local notation "hu" => Eq.mp (congrArg IsUnit ha) (Units.isUnit a)
local notation "hsNext" => show algebraMap R S (π ^ (start + (j + 1))) = 0 from by
  rw [← Nat.add_assoc, pow_succ, map_mul, hp, mul_zero]
local notation "conic" => coefficientShearRetainedScaleOneConic hπ data S r j hj 0 hj
  hs hp h3 h4 hr
local notation "N" => coefficientShearTerminalLaurent
  hπ data S r (j + 1) hj hsNext h3 h4 hc hr a ha
local notation "G" => coefficientShearGluedIso hπ data S r (j + 1) hj
local notation "hsAux" => show algebraMap R S (π ^ (start + j + 1)) = 0 from by
  rw [pow_succ, map_mul, hp, mul_zero]
local notation "P" => WeierstrassSuccessiveShearTerminal.laurentConicComponent
  W π (start + j + 1) (Data.b3 d) (Data.b4 d) (Data.b6 d) S r hsAux hp h3 h4 hr hc a ha
local notation "l" => WeierstrassSuccessiveShearTerminal.laurentConicComponentConic
  W π (start + j + 1) (Data.b3 d) (Data.b4 d) (Data.b6 d) S r hsAux hp h3 h4 hr hc a ha
local notation "t" => WeierstrassSuccessiveShearTerminal.laurentConicComponentTorus
  W π (start + j + 1) (Data.b3 d) (Data.b4 d) (Data.b6 d) S r hsAux hp h3 h4 hr hc a ha
local notation "p" => WeierstrassSuccessiveShearTerminal.laurentConicComponentStructure
  W π (start + j + 1) (Data.b3 d) (Data.b4 d) (Data.b6 d) S r hsAux hp h3 h4 hr hc a ha
local notation "J" => WeierstrassSuccessiveShearTerminal.laurentConicComponentProjectiveIso
  W π (start + j + 1) (Data.b3 d) (Data.b4 d) (Data.b6 d) S r hsAux hp h3 h4 hr hc a ha
local notation "g" => coefficientShearGluedStructure hπ data S r (j + 1) hj

local notation "M" => coefficientShearScaleOneLaurentComponentMap
  hπ data S r j hj hs hp h3 h4 hc hr a ha
local notation "C" => coefficientShearScaleOneEqualityComponent
  hπ data S r j hj hs hp h3 h4 hc hr a ha

/-- The entire original conic maps into its actual completed scale-one equality component. -/
@[irreducible] def coefficientShearScaleOneEqualityConicParameter :
    Spec (.of (ConicCoordinate (U).a₁ c)) ⟶ ProjectiveLine.scheme S := l ≫ (J).inv
local notation "q" => coefficientShearScaleOneEqualityConicParameter
  data S r j hj hp h3 h4 hc hr a ha

/-- The complete conic parameter recovers the actual original conic embedding. -/
@[reassoc] theorem coefficientShearScaleOneEqualityConicParameter_component : q ≫ C = conic := by
  rw [coefficientShearScaleOneEqualityConicParameter, coefficientShearScaleOneEqualityComponent]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  exact coefficientShearScaleOneLaurentComponentMap_conic ..

omit [IsDomain R] [IsBezout R] in
/-- The first original conic marking maps to zero of the completed component. -/
@[reassoc] theorem coefficientShearScaleOneEqualityConicParameter_first :
    Spec.map (CommRingCat.ofHom (conicFirstIncidencePoint (U).a₁ c hu).toRingHom) ≫ q =
      ProjectiveLine.zero S := by
  rw [coefficientShearScaleOneEqualityConicParameter, ← Category.assoc]
  change WeierstrassSuccessiveShearTerminal.laurentConicComponentFirstSection
    W π (start + j + 1) (Data.b3 d) (Data.b4 d) (Data.b6 d) S r hsAux hp h3 h4 hr hc a ha ≫
      (J).inv = _
  rw [← WeierstrassSuccessiveShearTerminal.laurentConicComponentProjectiveIso_zero]
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]

omit [IsDomain R] [IsBezout R] in
/-- The opposite original conic marking maps to infinity of the completed component. -/
@[reassoc] theorem coefficientShearScaleOneEqualityConicParameter_second :
    Spec.map (CommRingCat.ofHom (conicSecondIncidencePoint (U).a₁ c hu).toRingHom) ≫ q =
      ProjectiveLine.infinity S := by
  rw [coefficientShearScaleOneEqualityConicParameter, ← Category.assoc]
  change WeierstrassSuccessiveShearTerminal.laurentConicComponentSecondSection
    W π (start + j + 1) (Data.b3 d) (Data.b4 d) (Data.b6 d) S r hsAux hp h3 h4 hr hc a ha ≫
      (J).inv = _
  rw [← WeierstrassSuccessiveShearTerminal.laurentConicComponentProjectiveIso_infinity]
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- The full divided parameter recovers its actual atlas chart at scale-one equality. -/
@[reassoc] theorem coefficientShearScaleOneEqualityDividedParameter_component :
    coefficientShearEqualityDividedParameter data S r j hj hp h3 h4 hc hr a ha ≫ C =
      coefficientShearGluedChart hπ data S r (j + 1) hj (.inl 1) := by
  rw [coefficientShearEqualityDividedParameter]
  simp only [Category.assoc]
  rw [coefficientShearScaleOneEqualityComponent_torus, coefficientShearTerminalLaurent,
    Iso.inv_hom_id_assoc]

end FLT.Mazur.WeierstrassDividedDepth
