/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedRevisedRetainedReflection
public import FLT.Mazur.WeierstrassDividedRevisedClosingUnion
public import FLT.Mazur.WeierstrassDividedRevisedTargetLabels

/-!
# Reflection of every original retained/terminal equality

The cyclic labels force the last retained depth. The already constructed
embedding of the entire original closing union then reflects equality,
with both full source points and the actual terminal correction retained.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] finiteGlobalModel finiteGlobalContraction

/-- Morphism factorizations transport equality without expanding either chart. -/
theorem revisedComposite_points {X Y U V Z : Scheme} (f : X ⟶ U) (g : Y ⟶ V)
    (c : U ⟶ Z) (d : V ⟶ Z) (a : X ⟶ Z) (b : Y ⟶ Z)
    (ha : a = f ≫ c) (hb : b = g ≫ d) (x : X) (y : Y) (h : a x = b y) :
    c (f x) = d (g y) := by
  rw [ha, hb] at h
  exact h

/-- An embedded full union reflects point equality through both of its chart squares. -/
theorem revisedUnion_points {X Y U S T : Scheme} (f : X ⟶ U) (g : Y ⟶ U)
    (P : U ⟶ S) (J : U ⟶ T) [IsOpenImmersion J]
    (a : X ⟶ S) (b : Y ⟶ S) (F : X ⟶ T) (G : Y ⟶ T)
    (ha : f ≫ P = a) (hb : g ≫ P = b) (hF : f ≫ J = F) (hG : g ≫ J = G)
    (x : X) (y : Y) (h : F x = G y) : a x = b y := by
  have he := revisedComposite_points f g J J F G hF.symm hG.symm x y h
  have hs := congrArg P (J.isOpenEmbedding.injective he)
  change (f ≫ P) x = (g ≫ P) y at hs
  rw [ha, hb] at hs
  exact hs

variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (j : ℕ) (hj : j + 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "Q" => Quotient R π 1
local notation "τ" => arithmeticInitialMobiusSmoothing W H.a1_unit (π ^ 1) π 1
local notation "hn" => Fact.mk
  (arithmeticInitialFactorRatioSmoothing_nilpotent W H.a1_unit (π ^ 1) π 1 H.scale_div)
local notation "A" => arithmeticLabeledAtlasObject hπ data H 1 (j + 1) hj
local notation "a" => arithmeticLabeledAtlasMap hπ data H 1 (j + 1) hj
local notation "G" => arithmeticFirstOriginalRevisedChart hπ data H j hj u hu
local notation "F" => arithmeticFirstOriginalRevisedGlobalMap hπ data H j hj u hu

local notation "p" => arithmeticRevisedPolygonParameter data H 1 j hj u hu
local notation "σ" => arithmeticTerminalChangedSmoothing data H 1 j hj u hu
local notation "C" => arithmeticRetainedFixedSmoothingIso data H 1 (j + 1) hj
local notation "K" => arithmeticFirstResidualRetainedIso hπ data H j hj u hu
local notation "O" => twistedRetainedOrientation data H 1
local notation "E" => arithmeticFirstResidualAtlasIso hπ data H j hj u hu
local notation "l" => leftBranchOpen Q (parameter R π 1)
local notation "r" => arithmeticOriginalClosingBoundary data H 1 j hj
local notation "J" => arithmeticFirstOriginalRevisedClosingMap data H j hj u hu hπ
local notation "P" => originalClosingAttachmentToGlobal hπ data H 1 j hj

local notation "N" => arithmeticFirstRevisedRetainedNodeMap hπ data H j hj u hu
local notation "c" => arithmeticRevisedPolygonRetainedChart data H 1 j hj u hu
local notation "d" => arithmeticRevisedPolygonTerminalChart data H 1 j hj u hu

omit [IsBezout R] in
/-- Equality with any terminal point forces the last original retained depth. -/
theorem arithmeticFirstRevisedRetainedTerminal_location (idx : Fin (j + 1)) (b : Bool)
    (x : PolygonSmoothing.chart Q (parameter R π 1)) (y : A .terminal)
    (h : G (.retained idx b) x = G .terminal y) : idx.val = j := by
  apply arithmeticRevisedRetainedTerminal_location data H 1 j hj u hu idx b
    ((N idx b ≫ (O b).hom) x) ((E .terminal).hom y)
  exact revisedComposite_points (N idx b ≫ (O b).hom) (E .terminal).hom
    (c idx b) d (G (.retained idx b)) (G .terminal)
    (by
      rw [Category.assoc]
      exact arithmeticFirstRevisedRetainedNodeMap_chart hπ data H j hj u hu idx b) rfl x y h

/-- Each full original closing attachment embeds in the independent target. -/
instance arithmeticFirstRevisedClosing_isOpenImmersion (b : Bool) :
    IsOpenImmersion (J b) := by
  unfold arithmeticFirstOriginalRevisedClosingMap
  infer_instance

/-- The closing comparison is the restriction of the complete global comparison. -/
@[reassoc] theorem arithmeticFirstRevisedClosing_global (b : Bool) : P b ≫ F = J b := by
  apply pushout.hom_ext
  · rw [originalClosingAttachmentToGlobal_retained_assoc,
      arithmeticFirstOriginalRevisedGlobalMap_chart,
      arithmeticFirstOriginalRevisedRetainedMap_closing]
    rfl
  · rw [originalClosingAttachmentToGlobal_terminal_assoc,
      arithmeticFirstOriginalRevisedGlobalMap_chart,
      arithmeticFirstOriginalRevisedClosingMap_terminal_atlas]
    rfl

/-- The whole original last/terminal pair reflects equality through its open-union embedding. -/
theorem arithmeticFirstRevisedLastTerminal_points_eq (b : Bool)
    (x : PolygonSmoothing.chart Q (parameter R π 1)) (y : A .terminal)
    (h : G (.retained ⟨j, Nat.lt_succ_self j⟩ b) x = G .terminal y) :
    a (.retained ⟨j, Nat.lt_succ_self j⟩ b) x = a .terminal y := by
  exact revisedUnion_points (pushout.inl l (r b)) (pushout.inr l (r b)) (P b) (J b)
    _ _ _ _ (originalClosingAttachmentToGlobal_retained hπ data H 1 j hj b)
    (originalClosingAttachmentToGlobal_terminal hπ data H 1 j hj b)
    (arithmeticFirstOriginalRevisedRetainedMap_closing hπ data H j hj u hu b)
    (arithmeticFirstOriginalRevisedClosingMap_terminal_atlas hπ data H j hj u hu b) x y h

/-- Every original retained/terminal equality is already an equality in the source stage. -/
theorem arithmeticFirstRevisedRetainedTerminal_points_eq (idx : Fin (j + 1)) (b : Bool)
    (x : PolygonSmoothing.chart Q (parameter R π 1)) (y : A .terminal)
    (h : G (.retained idx b) x = G .terminal y) :
    a (.retained idx b) x = a .terminal y := by
  have hi := arithmeticFirstRevisedRetainedTerminal_location hπ data H j hj u hu idx b x y h
  have he : idx = ⟨j, Nat.lt_succ_self j⟩ := Fin.ext hi
  subst idx
  exact arithmeticFirstRevisedLastTerminal_points_eq hπ data H j hj u hu b x y h

end FLT.Mazur.WeierstrassDividedDepth
