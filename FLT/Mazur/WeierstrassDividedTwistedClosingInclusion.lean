/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedTwistedAtlasGluing

/-!
# Both transported closing pairs embed into the same complete target

The original pair unions are identified before transporting their inclusions.
Both target pairs share the single full terminal chart; the retained chart
inclusion incorporates the original polygon branch orientation.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX WeierstrassDilatation
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] finiteGlobalModel finiteGlobalContraction
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (m j : ℕ) (hj : j + 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "Q" => Quotient R π m
local notation "l" => leftBranchOpen Q (parameter R π m)
local notation "r" => arithmeticOriginalClosingBoundary data H m j hj
local notation "L" => arithmeticClosingRetainedBoundary data H m
local notation "M" => arithmeticClosingTerminalBoundary data H m j hj u hu
local notation "I" => arithmeticClosingAttachmentIso data H m j hj u hu
local notation "G" => simultaneousTwistedArithmeticIso hπ data H m j hj u hu
local notation "ι" => simultaneousTwistedArithmeticChart hπ data H m j hj u hu
local notation "C" => arithmeticRetainedFixedSmoothingIso data H m (j + 1) hj
  (Fin.mk j (Nat.lt_succ_self j))
local notation "d" => data (Fin.mk (j + 1) (Nat.lt_succ_of_le hj))
local notation "P" => fixedTerminalPolygonIso π W (π ^ (1 + j + 1))
  (Data.b3 d) (Data.b4 d) (Data.b6 d) H.a1_unit (H.scale (j + 1)) H.a2_div
  (H.b3_div _) (H.b4_div _) (H.b6_div _) u hu m
local notation "O" => twistedRetainedOrientation data H m
local notation "a" => fun b ↦ ArithmeticChartLabel.retained (Fin.mk j (Nat.lt_succ_self j)) b

/-- Both pair attachments map into the single target through their actual original open unions. -/
def twistedClosingInclusion (b : Bool) :
    arithmeticTwistedClosingAttachment data H m j hj u hu b ⟶
      simultaneousTwistedArithmeticStage hπ data H m j hj u hu :=
  (I b).inv ≫ originalClosingAttachmentToGlobal hπ data H m j hj b ≫ (G).hom

instance twistedClosingInclusion_isOpenImmersion (b : Bool) :
    IsOpenImmersion (twistedClosingInclusion hπ data H m j hj u hu b) := by
  unfold twistedClosingInclusion
  infer_instance

/-- The pair embedding recovers the original global union under the two comparisons. -/
@[reassoc] theorem twistedClosingInclusion_original (b : Bool) :
    (I b).hom ≫ twistedClosingInclusion hπ data H m j hj u hu b =
      originalClosingAttachmentToGlobal hπ data H m j hj b ≫ (G).hom := by
  rw [twistedClosingInclusion, Iso.hom_inv_id_assoc]

/-- The retained part of either attachment has the exact original polygon orientation. -/
@[reassoc] theorem twistedClosingInclusion_retained (b : Bool) :
    pushout.inl L (M b) ≫ twistedClosingInclusion hπ data H m j hj u hu b =
      (O b).hom ≫ ι (a b) := by
  apply (cancel_epi (C).hom).mp
  rw [← Category.assoc, ← arithmeticClosingAttachmentIso_retained,
    Category.assoc, twistedClosingInclusion_original,
    originalClosingAttachmentToGlobal_retained_assoc, simultaneousTwistedArithmeticIso_chart]
  rfl

/-- Both closing attachments use the very same full terminal chart in the complete target. -/
@[reassoc] theorem twistedClosingInclusion_terminal (b : Bool) :
    pushout.inr L (M b) ≫ twistedClosingInclusion hπ data H m j hj u hu b =
      ι .terminal := by
  apply (cancel_epi (P).hom).mp
  rw [← Category.assoc, ← arithmeticClosingAttachmentIso_terminal,
    Category.assoc, twistedClosingInclusion_original,
    originalClosingAttachmentToGlobal_terminal_assoc, simultaneousTwistedArithmeticIso_chart]
  rfl

/-- The exact transported terminal and oriented retained arrows agree in one common target. -/
@[reassoc] theorem simultaneousTwistedClosing_boundary (b : Bool) :
    L ≫ (O b).hom ≫ ι (a b) = M b ≫ ι .terminal := by
  calc
    L ≫ (O b).hom ≫ ι (a b) =
        L ≫ pushout.inl L (M b) ≫ twistedClosingInclusion hπ data H m j hj u hu b := by
      rw [twistedClosingInclusion_retained]
    _ = M b ≫ pushout.inr L (M b) ≫
        twistedClosingInclusion hπ data H m j hj u hu b := by
      rw [← Category.assoc, pushout.condition, Category.assoc]
    _ = M b ≫ ι .terminal := by rw [twistedClosingInclusion_terminal]

omit [IsDomain R] [IsBezout R] in
/-- The orientation agrees exactly with the prescribed retained polygon label convention. -/
theorem twistedRetainedOrientation_polygon (idx : Fin (j + 1)) (b : Bool) :
    let _ := Fact.mk
      (arithmeticInitialFactorRatioSmoothing_nilpotent W H.a1_unit (π ^ 1) π m (by simp))
    (O b).hom ≫ PolygonInfinitesimal.chart Q
      (arithmeticInitialMobiusSmoothing W H.a1_unit (π ^ 1) π m)
      (2 * (j + 1) + 3) (by omega) (retainedPolygonIndex (j + 1) idx b) =
    retainedPolygonMap Q (arithmeticInitialMobiusSmoothing W H.a1_unit (π ^ 1) π m)
      (j + 1) idx b := by
  dsimp only
  cases b <;> rfl

end FLT.Mazur.WeierstrassDividedDepth
