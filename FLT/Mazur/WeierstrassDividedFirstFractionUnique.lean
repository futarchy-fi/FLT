/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedFirstFractionCenter
public import FLT.Mazur.WeierstrassDividedGlobalStepOriginal

/-!
# Uniqueness after flat restriction of actual first-successor action lifts

A flat affine restriction retains the regular principal output center.
The full unchanged-center pullbacks therefore force any two lifts of the
same actual output to agree in the whole finite successor model.
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

/-- The constructed local action is the unique lift after any flat affine restriction. -/
theorem firstFractionAction_flat_unique (i : (U).I₀) {S : Type u} [CommRing S]
    (p : Spec (.of S) ⟶ Spec ((U).X i)) [Flat p]
    (a : Spec (.of S) ⟶ finiteGlobalModel hπ data 1 hn)
    (ha : a ≫ finiteGlobalStep hπ data 0 hn =
      p ≫ firstFractionAction hπ data hn f hf i ≫ finiteGlobalStep hπ data 0 hn) :
    a = p ≫ firstFractionAction hπ data hn f hf i := by
  let ψ := affineChartRingHom p
  have hp : Spec.map (CommRingCat.ofHom ψ) = p := affineChartRingHom_spec p
  have hflat : RingHom.Flat ψ := by
    apply (Flat.SpecMap_iff (f := CommRingCat.ofHom ψ)).mp
    rw [hp]
    infer_instance
  have hc : (p ≫ firstFractionAction hπ data hn f hf i) ≫
      finiteGlobalStep hπ data 0 hn =
        Spec.map (CommRingCat.ofHom
          (ψ.comp (firstFractionAlpha hπ data hn f hf i))) ≫ v := by
    rw [Category.assoc, firstFractionAction_step, CommRingCat.ofHom_comp,
      Spec.map_comp, Category.assoc, hp, firstFractionAlpha_spec]
  apply finiteGlobalStep_regular_center_ext hπ data 0 hn
    (ψ.comp (firstFractionAlpha hπ data hn f hf i))
    (ψ (firstFractionDenominator hπ data hn f hf i))
    (firstFractionAlpha_mapped_center hπ data hn f hf i ψ)
    (firstFractionDenominator_mapped_regular hπ data hn f hf i ψ hflat)
    a (p ≫ firstFractionAction hπ data hn f hf i)
  · exact ha.trans ((Category.assoc _ _ _).symm.trans hc)
  · exact hc

/-- The precise step contraction characterizes each actual affine local action. -/
theorem firstFractionAction_unique (i : (U).I₀)
    (a : Spec ((U).X i) ⟶ finiteGlobalModel hπ data 1 hn)
    (ha : a ≫ finiteGlobalStep hπ data 0 hn =
      firstFractionDividedOutput hπ data hn f hf i ≫ v) :
    a = firstFractionAction hπ data hn f hf i := by
  have he := firstFractionAction_flat_unique hπ data hn f hf i (𝟙 _) a (by
    rw [Category.id_comp, firstFractionAction_step]
    exact ha)
  simpa only [Category.id_comp] using he

end FLT.Mazur.WeierstrassDividedDepth
