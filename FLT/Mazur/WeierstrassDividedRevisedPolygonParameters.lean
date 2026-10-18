/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedTerminalChangedSmoothing
public import FLT.Mazur.WeierstrassDividedInitialPolygonLabels
public import FLT.Mazur.WeierstrassModificationXArithmeticFactorRatioNilpotence

/-!
# The revised polygon's actual node parameters

Terminal label zero uses the proved changed smoothing. Every initial and
retained label keeps the original smoothing. Both parameters are nilpotent
and their original arithmetic coefficient squares are proved explicitly.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages WeierstrassModificationX
variable {R : Type} [CommRing R] {W : WeierstrassCurve R} {π : R} {n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (m j : ℕ) (hj : j + 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "Q" => Quotient R π m
local notation "τ" => arithmeticInitialMobiusSmoothing W H.a1_unit (π ^ 1) π m
local notation "σ" => arithmeticTerminalChangedSmoothing data H m j hj u hu

/-- The exact terminal smoothing is nilpotent at every arithmetic order. -/
theorem arithmeticTerminalChangedSmoothing_nilpotent : IsNilpotent σ := by
  unfold arithmeticTerminalChangedSmoothing
  exact (Commute.all _ _).isNilpotent_mul_left
    (arithmeticInitialFactorRatioSmoothing_nilpotent W H.a1_unit (π ^ 1) π m H.scale_div)

/-- The revised polygon retains a distinct terminal parameter at its original cyclic label. -/
def arithmeticRevisedPolygonParameter (i : Fin (2 * (j + 1) + 3)) : Q :=
  if i = 0 then σ else τ

/-- The common terminal has exactly its changed smoothing, without a fixed-parameter claim. -/
theorem arithmeticRevisedPolygonParameter_terminal :
    arithmeticRevisedPolygonParameter data H m j hj u hu 0 = σ := ite_eq_left rfl

/-- All other nodes have the unchanged original normalized smoothing. -/
theorem arithmeticRevisedPolygonParameter_nonterminal
    (i : Fin (2 * (j + 1) + 3)) (hi : i ≠ 0) :
    arithmeticRevisedPolygonParameter data H m j hj u hu i = τ := ite_eq_right hi

/-- Neither retained arm overwrites the shared terminal label. -/
theorem retainedPolygonIndex_ne_terminal (k : ℕ) (a : Fin k) (b : Bool) :
    retainedPolygonIndex k a b ≠ 0 := by
  intro h
  have hv := congrArg Fin.val h
  cases b <;> simp only [retainedPolygonIndex, Bool.false_eq_true,
    ↓reduceIte, Fin.val_zero] at hv <;> omega

/-- Every original retained label keeps its original smoothing. -/
theorem arithmeticRevisedPolygonParameter_retained (a : Fin (j + 1)) (b : Bool) :
    arithmeticRevisedPolygonParameter data H m j hj u hu
      (retainedPolygonIndex (j + 1) a b) = τ :=
  arithmeticRevisedPolygonParameter_nonterminal data H m j hj u hu _
    (retainedPolygonIndex_ne_terminal _ a b)

/-- Both original initial labels keep the unchanged smoothing. -/
theorem arithmeticRevisedPolygonParameter_initial (b : Bool) :
    arithmeticRevisedPolygonParameter data H m j hj u hu
      (initialPolygonIndex (j + 1) b) = τ :=
  arithmeticRevisedPolygonParameter_nonterminal data H m j hj u hu _
    (initialPolygonIndex_ne_terminal _ b)

instance arithmeticRevisedPolygonParameter_nilpotent (i : Fin (2 * (j + 1) + 3)) :
    Fact (IsNilpotent (arithmeticRevisedPolygonParameter data H m j hj u hu i)) := by
  constructor
  unfold arithmeticRevisedPolygonParameter
  split_ifs
  · exact arithmeticTerminalChangedSmoothing_nilpotent data H m j hj u hu
  · exact arithmeticInitialFactorRatioSmoothing_nilpotent W H.a1_unit (π ^ 1) π m H.scale_div

variable [IsDomain R] (hπ : π ≠ 0)
include hπ

/-- Every node parameter follows the actual quotient homomorphism. -/
theorem arithmeticRevisedPolygonParameter_restriction (i : Fin (2 * (j + 1) + 3)) :
    restriction R π m (arithmeticRevisedPolygonParameter data H (m + 1) j hj u hu i) =
      arithmeticRevisedPolygonParameter data H m j hj u hu i := by
  unfold arithmeticRevisedPolygonParameter
  split_ifs
  · exact arithmeticTerminalChangedSmoothing_restriction data H m j hj u hu hπ
  · exact arithmeticInitialMobiusSmoothing_restriction W H.a1_unit (π ^ 1) π m

end FLT.Mazur.WeierstrassDividedDepth
