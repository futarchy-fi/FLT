/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientShearRootEqualityComponent
import all FLT.Mazur.WeierstrassCoefficientShearRetainedFiber

/-!
# Full original chart parameters inside the completed equality component

Extract the entire conic and divided equation, including both incidence markings.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassSuccessiveX WeierstrassModificationX WeierstrassDilatation
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option quotPrecheck false
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (S : Type u) [Field S] [Algebra R S] (r : S) (j : ℕ) (hj : j + 1 ≤ n)
local notation "d" => data (Fin.mk (j + 1) (Nat.lt_succ_of_le hj))
variable (hs : algebraMap R S (π ^ (start + j)) = 0) (hp : algebraMap R S π = 0)
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
local notation "conic" => coefficientShearRetainedConic hπ data S r (j + 1) hj
  (Fin.mk j (Nat.lt_succ_self j)) hs hp h3 h4 hr
local notation "N" => coefficientShearTerminalLaurent
  hπ data S r (j + 1) hj hsNext h3 h4 hc hr a ha
local notation "G" => coefficientShearGluedIso hπ data S r (j + 1) hj
local notation "ψ" => tensorShearTerminalLaurentConicMap W π (start + j)
  (Data.b3 d) (Data.b4 d) (Data.b6 d) S r hs hp h3 h4 hr hc a ha
local notation "b" => Spec.map (CommRingCat.ofHom (AlgHom.toRingHom ψ))
local notation "inc" => PrincipalOpenTransport.inclusion (conicT (U).a₁ c)
local notation "F" => tensorShearConicBoundaryIso W (π ^ (start + j)) π
  (Data.b3 d) (Data.b4 d) (Data.b6 d) S r hs hp h3 h4 hr
local notation "T" => tensorShearTerminalLaurentEquiv W π (start + j)
  (Data.b3 d) (Data.b4 d) (Data.b6 d) S r hp h3 h4 hr hc a ha

local notation "P" => WeierstrassSuccessiveShearTerminal.laurentConicComponent
  W π (start + j) (Data.b3 d) (Data.b4 d) (Data.b6 d) S r hs hp h3 h4 hr hc a ha
local notation "l" => WeierstrassSuccessiveShearTerminal.laurentConicComponentConic
  W π (start + j) (Data.b3 d) (Data.b4 d) (Data.b6 d) S r hs hp h3 h4 hr hc a ha
local notation "t" => WeierstrassSuccessiveShearTerminal.laurentConicComponentTorus
  W π (start + j) (Data.b3 d) (Data.b4 d) (Data.b6 d) S r hs hp h3 h4 hr hc a ha
local notation "p" => WeierstrassSuccessiveShearTerminal.laurentConicComponentStructure
  W π (start + j) (Data.b3 d) (Data.b4 d) (Data.b6 d) S r hs hp h3 h4 hr hc a ha
local notation "J" => WeierstrassSuccessiveShearTerminal.laurentConicComponentProjectiveIso
  W π (start + j) (Data.b3 d) (Data.b4 d) (Data.b6 d) S r hs hp h3 h4 hr hc a ha
local notation "g" => coefficientShearGluedStructure hπ data S r (j + 1) hj

local notation "M" => coefficientShearRootLaurentComponentMap
  hπ data S r j hj hs hp h3 h4 hc hr a ha
local notation "C" => coefficientShearRootEqualityComponent
  hπ data S r j hj hs hp h3 h4 hc hr a ha

/-- The entire original conic, with its nonzero constant, maps to the completed component. -/
@[irreducible] def coefficientShearEqualityConicParameter :
    Spec (.of (ConicCoordinate (U).a₁ c)) ⟶ ProjectiveLine.scheme S := l ≫ (J).inv
local notation "q" => coefficientShearEqualityConicParameter
  data S r j hj hs hp h3 h4 hc hr a ha

/-- The extracted full conic recovers the actual retained conic immersion. -/
@[reassoc] theorem coefficientShearEqualityConicParameter_component : q ≫ C = conic := by
  rw [coefficientShearEqualityConicParameter, coefficientShearRootEqualityComponent]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  exact coefficientShearRootLaurentComponentMap_conic ..

omit [IsDomain R] [IsBezout R] in
/-- The original first conic marking is exactly zero of the complete equality component. -/
@[reassoc] theorem coefficientShearEqualityConicParameter_first :
    Spec.map (CommRingCat.ofHom (conicFirstIncidencePoint (U).a₁ c hu).toRingHom) ≫ q =
      ProjectiveLine.zero S := by
  rw [coefficientShearEqualityConicParameter, ← Category.assoc]
  change WeierstrassSuccessiveShearTerminal.laurentConicComponentFirstSection
    W π (start + j) (Data.b3 d) (Data.b4 d) (Data.b6 d) S r hs hp h3 h4 hr hc a ha ≫
      (J).inv = _
  rw [← WeierstrassSuccessiveShearTerminal.laurentConicComponentProjectiveIso_zero]
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]

omit [IsDomain R] [IsBezout R] in
/-- The original opposite marking is infinity of the same completed component. -/
@[reassoc] theorem coefficientShearEqualityConicParameter_second :
    Spec.map (CommRingCat.ofHom (conicSecondIncidencePoint (U).a₁ c hu).toRingHom) ≫ q =
      ProjectiveLine.infinity S := by
  rw [coefficientShearEqualityConicParameter, ← Category.assoc]
  change WeierstrassSuccessiveShearTerminal.laurentConicComponentSecondSection
    W π (start + j) (Data.b3 d) (Data.b4 d) (Data.b6 d) S r hs hp h3 h4 hr hc a ha ≫
      (J).inv = _
  rw [← WeierstrassSuccessiveShearTerminal.laurentConicComponentProjectiveIso_infinity]
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]

local notation "e" => coefficientShearLaurentEquiv W (π ^ (start + (j + 1)))
  (Data.b3 d) (Data.b4 d) (Data.b6 d) S r hsNext h3 h4 hr a ha hc
local notation "E" => Scheme.Spec.mapIso (e).toRingEquiv.toCommRingCatIso.op

/-- The entire actual divided atlas equation maps to the original projective parameter. -/
@[irreducible] def coefficientShearEqualityDividedParameter :
    coefficientShearAtlasObject data S r (j + 1) hj (.inl 1) ⟶
      ProjectiveLine.scheme S :=
  (E).inv ≫ ProjectiveLine.overlapLeft S ≫ ProjectiveLine.left S
local notation "v" => coefficientShearEqualityDividedParameter
  data S r j hj hp h3 h4 hc hr a ha

omit [IsDomain R] [IsBezout R] in
/-- The normalized parameter is the full original terminal torus. -/
@[reassoc] theorem coefficientShearEqualityDividedParameter_laurent :
    (E).hom ≫ v = ProjectiveLine.overlapLeft S ≫ ProjectiveLine.left S := by
  rw [coefficientShearEqualityDividedParameter, Iso.hom_inv_id_assoc]

/-- The full divided parameter recovers the original atlas chart through the actual component. -/
@[reassoc] theorem coefficientShearEqualityDividedParameter_component :
    v ≫ C = coefficientShearGluedChart hπ data S r (j + 1) hj (.inl 1) := by
  rw [coefficientShearEqualityDividedParameter]
  simp only [Category.assoc]
  rw [coefficientShearRootEqualityComponent_torus, coefficientShearTerminalLaurent,
    Iso.inv_hom_id_assoc]

end FLT.Mazur.WeierstrassDividedDepth
