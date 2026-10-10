/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedLaurentTerminalMap
public import FLT.Mazur.WeierstrassSuccessiveXTerminalLaurentMarks
public import FLT.Mazur.WeierstrassDividedTerminalParameterOrigins

/-!
# Original coefficient structure and attachments of the equality-depth component

The glued map is over the residue field. Its two marked sections recover
exactly the original ordered sections in the finite model, at positive
scale and at scale one.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
open scoped LaurentPolynomial
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassSuccessiveX WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (D : SplitNodeDepth W π depth) (j : ℕ) (hj : j + 1 ≤ n)
  (hk : 2 * (start + j + 1) ≤ depth)
local notation "K" => ResidueField R
local notation "d" => data (Fin.mk (j + 1) (Nat.lt_succ_of_le hj))
local notation "a" => WeierstrassCurve.a₁ (W.map (residue R))
local notation "c" => residue R (Data.b6 d)
local notation "C₀" => ConicCoordinate a c
local notation "B" => MiddleConicOpen (W.map (residue R)) c
local notation "i" => Spec.map (CommRingCat.ofHom (algebraMap C₀ B))
local notation "g" => globalSuccessiveTensorChart hπ data K j hj
local notation "X" => finiteGlobalTensorModel hπ data K (j + 1) hj

local notation "C" => laurentTerminalOriginalConic hπ data D j hj hk
variable (hp : 2 * (start + j + 1) = depth)
local notation "ψ" => residueLaurentConicMap D (start + j) hk
  (Data.b3 d) (Data.b4 d) (Data.b6 d) (Data.factor3 d) (Data.factor4 d) (Data.factor6 d) hp
local notation "s" => Spec.map (CommRingCat.ofHom (AlgHom.toRingHom ψ))
local notation "G" => terminalLaurentChart hπ data D (j + 1) hj
  (Nat.zero_lt_succ (start + j)) hk hp
local notation "P" => laurentConicComponent D (start + j) hk
  (Data.b3 d) (Data.b4 d) (Data.b6 d) (Data.factor3 d) (Data.factor4 d) (Data.factor6 d) hp
local notation "l" => laurentConicComponentConic D (start + j) hk
  (Data.b3 d) (Data.b4 d) (Data.b6 d) (Data.factor3 d) (Data.factor4 d) (Data.factor6 d) hp
local notation "r" => laurentConicComponentTorus D (start + j) hk
  (Data.b3 d) (Data.b4 d) (Data.b6 d) (Data.factor3 d) (Data.factor4 d) (Data.factor6 d) hp

local notation "f" => laurentTerminalComponentMap hπ data D j hj hk hp

local notation "p" => laurentConicComponentStructure D (start + j) hk
  (Data.b3 d) (Data.b4 d) (Data.b6 d) (Data.factor3 d) (Data.factor4 d) (Data.factor6 d) hp
local notation "q" => Spec.map (CommRingCat.ofHom (algebraMap R K))
local notation "b" => pullback.fst q (finiteGlobalStructure hπ data (j + 1) hj)

/-- The complete original conic keeps its residue-field structure at every scale. -/
@[reassoc] theorem laurentTerminalOriginalConic_structure : C ≫ b = conicStructure a c := by
  by_cases h : 0 < start + j
  · rw [laurentTerminalOriginalConic_positive hπ data D j hj hk h,
      Category.assoc, globalSuccessiveTensorChart_structure,
      residueSuccessiveConicImmersion_eq_spec]
    exact terminalComponent_algebra_structure
      (residueSuccessiveConicMap D (start + j) h hk
        (Data.b3 d) (Data.b4 d) (Data.b6 d) (Data.factor3 d) (Data.factor4 d))
  · rw [laurentTerminalOriginalConic_zero hπ data D j hj hk (by omega),
      Category.assoc, globalSuccessiveTensorChart_structure, zeroResidueConicImmersion,
      Category.assoc, zeroResidueFiberIso_structure]
    exact terminalComponent_algebra_structure (fiberConicMap a c)

/-- The full glued component map is over the original residue field. -/
@[reassoc] theorem laurentTerminalComponentMap_structure : f ≫ b = p := by
  apply laurentConicComponent_hom_ext D (start + j) hk
    (Data.b3 d) (Data.b4 d) (Data.b6 d) (Data.factor3 d) (Data.factor4 d) (Data.factor6 d) hp
  · rw [laurentTerminalComponentMap_conic_assoc, laurentTerminalOriginalConic_structure,
      laurentConicComponentConic_structure]
  · rw [laurentTerminalComponentMap_torus_assoc, terminalLaurentChart_structure,
      laurentConicComponentTorus_structure]

local notation "mFirst" => laurentConicComponentFirstSection D (start + j) hk
  (Data.b3 d) (Data.b4 d) (Data.b6 d) (Data.factor3 d) (Data.factor4 d) (Data.factor6 d) hp

/-- At positive scale the first marking is exactly the original ordered attachment. -/
@[reassoc] theorem laurentTerminalComponentMap_first_positive (h : 0 < start + j) :
    mFirst ≫ f = olderGlobalFirstSection hπ data D j hj 0 hj h hk := by
  rw [laurentConicComponentFirstSection, Category.assoc,
    laurentTerminalComponentMap_conic, laurentTerminalOriginalConic_positive hπ data D j hj hk h]
  rw [← terminalConicFirstParameter_origin hπ data D j hj hk h]
  simp only [terminalConicFirstParameter, Category.assoc,
    conicFirstParameterIso_origin_assoc]

/-- At scale one the first marking is exactly the original initial attachment. -/
@[reassoc] theorem laurentTerminalComponentMap_first_zero (h : start + j = 0) :
    mFirst ≫ f = olderGlobalZeroFirstSection hπ data D j hj 0 hj h hk := by
  rw [laurentConicComponentFirstSection, Category.assoc,
    laurentTerminalComponentMap_conic, laurentTerminalOriginalConic_zero hπ data D j hj hk h]
  rw [← terminalZeroConicFirstParameter_origin hπ data D j hj hk h]
  simp only [terminalZeroConicFirstParameter, Category.assoc,
    conicFirstParameterIso_origin_assoc]

local notation "mSecond" => laurentConicComponentSecondSection D (start + j) hk
  (Data.b3 d) (Data.b4 d) (Data.b6 d) (Data.factor3 d) (Data.factor4 d) (Data.factor6 d) hp

/-- At positive scale the second marking is exactly the original ordered attachment. -/
@[reassoc] theorem laurentTerminalComponentMap_second_positive (h : 0 < start + j) :
    mSecond ≫ f = olderGlobalSecondSection hπ data D j hj 0 hj h hk := by
  rw [laurentConicComponentSecondSection, Category.assoc,
    laurentTerminalComponentMap_conic, laurentTerminalOriginalConic_positive hπ data D j hj hk h]
  rw [← terminalConicSecondParameter_origin hπ data D j hj hk h]
  simp only [terminalConicSecondParameter, Category.assoc,
    conicSecondParameterIso_origin_assoc]

/-- At scale one the second marking is exactly the original initial attachment. -/
@[reassoc] theorem laurentTerminalComponentMap_second_zero (h : start + j = 0) :
    mSecond ≫ f = olderGlobalZeroSecondSection hπ data D j hj 0 hj h hk := by
  rw [laurentConicComponentSecondSection, Category.assoc,
    laurentTerminalComponentMap_conic, laurentTerminalOriginalConic_zero hπ data D j hj hk h]
  rw [← terminalZeroConicSecondParameter_origin hπ data D j hj hk h]
  simp only [terminalZeroConicSecondParameter, Category.assoc,
    conicSecondParameterIso_origin_assoc]

end FLT.Mazur.WeierstrassDividedDepth
