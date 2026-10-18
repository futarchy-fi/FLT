/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedRevisedClosingOriginal
public import FLT.Mazur.WeierstrassDividedResidualLiftAtlasFirstIdentification

/-!
# The revised closing maps use the existing first-order atlas identification

The independently constructed target comparisons are identified with the exact
whole-chart corrections in the original first-order atlas. The lifted terminal
uses its proved parameter identification rather than a fixed-parameter shortcut.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] [IsDomain R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (j : ℕ) (hj : j + 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "Q" => Quotient R π 1
local notation "l" => leftBranchOpen Q (parameter R π 1)
local notation "r" => arithmeticOriginalClosingBoundary data H 1 j hj
local notation "G" => arithmeticFirstOriginalRevisedClosingMap data H j hj u hu hπ
local notation "E" => arithmeticFirstResidualAtlasIso hπ data H j hj u hu
local notation "c" => arithmeticRevisedPolygonRetainedChart data H 1 j hj u hu
local notation "d" => arithmeticRevisedPolygonTerminalChart data H 1 j hj u hu

local notation "C" => arithmeticRetainedFixedSmoothingIso data H 1 (j + 1) hj
  (Fin.mk j (Nat.lt_succ_self j))
local notation "A₀" => arithmeticFirstResidualRetainedIso hπ data H j hj u hu
local notation "O" => twistedRetainedOrientation data H 1

/-- The retained restriction is exactly the previously constructed whole-chart correction. -/
@[reassoc] theorem arithmeticFirstOriginalRevisedClosingMap_retained_atlas (b : Bool) :
    pushout.inl l (r b) ≫ G b = (E (.retained ⟨j, by omega⟩ b)).hom ≫ c ⟨j, by omega⟩ b := by
  have hi : changedArithmeticAtlasIso hπ data H 1 j hj u hu
      (.retained ⟨j, by omega⟩ b) = C ≪≫ O b := by
    change (C ≪≫ O b) ≪≫ (Iso.refl _).symm = C ≪≫ O b
    exact Iso.trans_refl _
  rw [arithmeticFirstOriginalRevisedClosingMap_retained, arithmeticFirstResidualAtlasIso, hi]
  simp only [Iso.trans_hom, arithmeticFirstResidualAtlasCorrection, ↓reduceIte, Category.assoc]
  rw [arithmeticFirstResidualOrientedIso_hom_assoc]

/-- Both original terminal restrictions use the exact common first-order atlas correction. -/
@[reassoc] theorem arithmeticFirstOriginalRevisedClosingMap_terminal_atlas (b : Bool) :
    pushout.inr l (r b) ≫ G b = (E .terminal).hom ≫ d := by
  rw [arithmeticFirstOriginalRevisedClosingMap_terminal]
  simp only [arithmeticFirstResidualAtlasIso, changedArithmeticAtlasIso,
    twistedArithmeticAtlasIso, changedArithmeticAtlasToTwisted,
    arithmeticFirstResidualAtlasCorrection, Iso.trans_hom, Iso.symm_symm_eq, Category.assoc]

local notation "A" => arithmeticResidualLiftAtlasIso hπ data H 1 j hj u hu
local notation "J" => arithmeticResidualLiftAtlasFirstIdentification hπ data H j hj u hu

/-- The lifted terminal comparison reaches the revised target through its proved identification. -/
@[reassoc] theorem arithmeticFirstOriginalRevisedClosingMap_terminal_lifted (b : Bool) :
    pushout.inr l (r b) ≫ G b = (A .terminal).hom ≫ (J .terminal).hom ≫ d := by
  rw [arithmeticFirstOriginalRevisedClosingMap_terminal_atlas]
  have he := congrArg Iso.hom (arithmeticResidualLiftAtlasIso_first hπ data H j hj u hu
    .terminal)
  rw [Iso.trans_hom] at he
  rw [← he, Category.assoc]

/-- The original retained labels also keep the full lifted first-order correction. -/
@[reassoc] theorem arithmeticFirstOriginalRevisedClosingMap_retained_lifted (b : Bool) :
    pushout.inl l (r b) ≫ G b =
      (A (.retained ⟨j, by omega⟩ b)).hom ≫ (J (.retained ⟨j, by omega⟩ b)).hom ≫
        c ⟨j, by omega⟩ b := by
  rw [arithmeticFirstOriginalRevisedClosingMap_retained_atlas]
  have he := congrArg Iso.hom (arithmeticResidualLiftAtlasIso_first hπ data H j hj u hu
    (.retained ⟨j, by omega⟩ b))
  rw [Iso.trans_hom] at he
  rw [← he, Category.assoc]

end FLT.Mazur.WeierstrassDividedDepth
