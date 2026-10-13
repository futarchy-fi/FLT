/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientShearScaleOneEqualityParameters
public import FLT.Mazur.WeierstrassCoefficientShearEqualityChartParameters
import all FLT.Mazur.WeierstrassCoefficientShearRetainedScaleOneConic

/-!
# The original scale-one equality parameter on the full Laurent boundary

The actual scale-one transition has the same complete parameter as its
independently completed conic, including the original nonzero constant.
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

local notation "q" => coefficientShearScaleOneEqualityConicParameter
  data S r j hj hp h3 h4 hc hr a ha
local notation "ψ" => tensorShearScaleOneTerminalLaurentConicMap W π (start + j)
  (Data.b3 d) (Data.b4 d) (Data.b6 d) S r hs hp h3 h4 hr hc a ha
local notation "b" => Spec.map (CommRingCat.ofHom (AlgHom.toRingHom ψ))
local notation "inc" => PrincipalOpenTransport.inclusion (conicT (U).a₁ c)

omit [IsDomain R] [IsBezout R] in
/-- The original scale-one boundary preserves the entire completed projective parameter. -/
@[reassoc] theorem coefficientShearScaleOneEqualityConicParameter_boundary :
    inc ≫ q = b ≫ ProjectiveLine.overlapLeft S ≫ ProjectiveLine.left S := by
  apply (cancel_mono (J).hom).mp
  rw [coefficientShearScaleOneEqualityConicParameter]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [WeierstrassSuccessiveShearTerminal.laurentConicComponentProjectiveIso_torus]
  rw [tensorShearScaleOneTerminalLaurentConicMap_eq]
  exact pushout.condition

end FLT.Mazur.WeierstrassDividedDepth
