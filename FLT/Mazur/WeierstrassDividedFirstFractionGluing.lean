/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedFirstFractionUnique
public import FLT.Mazur.SchemeAffineFlatLiftGluing

/-!
# Gluing the actual first-successor fraction-input action

Flat uniqueness identifies the local maps on each entire scheme-theoretic
affine overlap. They glue to a map on the full simultaneous fraction-input
and divided-output domain, with its prescribed global step contraction.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val)) (hn : 1 ≤ n)
  (f : WeierstrassDilatation.Coordinate W (π ^ (start + 0))
    (π * (data ⟨1, Nat.lt_succ_of_le hn⟩).b3)
    (π * (data ⟨1, Nat.lt_succ_of_le hn⟩).b4)
    (π ^ 2 * (data ⟨1, Nat.lt_succ_of_le hn⟩).b6))
  (hf : f ∈ WeierstrassSuccessiveX.modificationCenter W (π ^ (start + 0)) π
    (data ⟨1, Nat.lt_succ_of_le hn⟩).b3
    (data ⟨1, Nat.lt_succ_of_le hn⟩).b4
    (data ⟨1, Nat.lt_succ_of_le hn⟩).b6)
local notation "e" => data (Fin.mk 1 (Nat.lt_succ_of_le hn))
local notation "B" => WeierstrassDilatation.Coordinate W (π ^ (start + 0))
  (π * (Data.b3 e)) (π * (Data.b4 e)) (π ^ 2 * (Data.b6 e))
local notation "I" => WeierstrassSuccessiveX.modificationCenter W (π ^ (start + 0)) π
  (Data.b3 e) (Data.b4 e) (Data.b6 e)
local notation "C" => BlowupFractionChart.chart I f
local notation "c" => finiteSuccessiveFractionChart hπ data 0 hn f hf
local notation "v" => finiteNormalizedChart hπ data 0 hn

local notation "d" => data (Fin.mk 0 (Nat.zero_lt_succ n))
local notation "q" => previousOriginalMap hπ d e
local notation "U" => firstFractionCover hπ data hn f hf


local notation "E" => initialExterior d

/-- Local lifts agree on every full intersection of actual affine domain members. -/
theorem firstFractionAction_overlap (i j : (U).I₀) :
    pullback.fst ((U).f i) ((U).f j) ≫ firstFractionAction hπ data hn f hf i =
      pullback.snd ((U).f i) ((U).f j) ≫ firstFractionAction hπ data hn f hf j :=
  SchemeAffineFlatLiftGluing.compatible (U) (firstFractionAction hπ data hn f hf)
    (finiteGlobalStep hπ data 0 hn) (pullback.fst _ _ ≫ firstFractionOutput hπ data hn f hf)
    (fun k => firstFractionAction_output hπ data hn f hf k)
    (fun k _ _ p _ a ha => firstFractionAction_flat_unique hπ data hn f hf k p a ha) i j

/-- The action lift on the entire actual simultaneous fraction/divided domain. -/
irreducible_def firstFractionDomainAction : firstFractionDomain hπ data hn f hf ⟶
    finiteGlobalModel hπ data 1 hn :=
  (U).openCover.glueMorphisms (firstFractionAction hπ data hn f hf)
    (firstFractionAction_overlap hπ data hn f hf)

/-- The glued map recovers every previously constructed affine action lift. -/
@[reassoc] theorem firstFractionCover_action (i : (U).I₀) :
    (U).f i ≫ firstFractionDomainAction hπ data hn f hf =
      firstFractionAction hπ data hn f hf i := by
  rw [firstFractionDomainAction_def]
  exact (U).openCover.ι_glueMorphisms _ _ i

/-- The glued map retains the full normalized divided output. -/
@[reassoc] theorem firstFractionDomainAction_step :
    firstFractionDomainAction hπ data hn f hf ≫ finiteGlobalStep hπ data 0 hn =
      pullback.snd _ _ ≫ v := by
  apply (U).openCover.hom_ext
  intro i
  simp only [Scheme.AffineOpenCover.openCover_f]
  rw [firstFractionCover_action_assoc, firstFractionAction_step]
  exact Category.assoc _ _ _

/-- Its step contraction is exactly the existing initial action on the actual source. -/
@[reassoc] theorem firstFractionDomainAction_output :
    firstFractionDomainAction hπ data hn f hf ≫ finiteGlobalStep hπ data 0 hn =
      pullback.fst _ _ ≫ firstFractionOutput hπ data hn f hf := by
  rw [firstFractionDomainAction_step, pullback.condition]

/-- The original contraction is the genuine smooth action on the whole fraction input. -/
@[reassoc] theorem firstFractionDomainAction_original :
    firstFractionDomainAction hπ data hn f hf ≫ finiteGlobalContraction hπ data 1 hn =
      pullback.fst _ _ ≫ firstFractionInput hπ data hn f hf ≫
        finiteGlobalActionInput hπ data 1 hn ≫ leftSmoothFactorAddition W := by
  rw [← finiteGlobalStep_contraction hπ data 0 hn, firstFractionDomainAction_output_assoc]
  simp only [firstFractionOutput, Category.assoc, firstActionOutput_contraction]

/-- The prescribed output characterizes the glued map among all maps from the full domain. -/
theorem firstFractionDomainAction_unique
    (a : firstFractionDomain hπ data hn f hf ⟶ finiteGlobalModel hπ data 1 hn)
    (ha : a ≫ finiteGlobalStep hπ data 0 hn = pullback.snd _ _ ≫ v) :
    a = firstFractionDomainAction hπ data hn f hf := by
  apply (U).openCover.hom_ext
  intro i
  simp only [Scheme.AffineOpenCover.openCover_f]
  rw [firstFractionCover_action]
  apply firstFractionAction_unique hπ data hn f hf i
  rw [Category.assoc, ha]
  exact (Category.assoc _ _ _).symm

end FLT.Mazur.WeierstrassDividedDepth
