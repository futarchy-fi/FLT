/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedFirstFractionDomain
public import FLT.Mazur.WeierstrassDividedFirstActionAtlas

/-!
# Actual open embeddings of the fraction action domains

The fraction-input product and its simultaneous divided-output domain
are open subschemes of the whole prescribed action source. The comparison
with the full divided-output domain retains both its projections.
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

/-- Fraction input products are actual open subschemes of the full action product. -/
instance firstFractionInput_isOpenImmersion :
    IsOpenImmersion (firstFractionInput hπ data hn f hf) := by
  have he : firstFractionInput hπ data hn f hf =
      pullback.map (integralSmoothStructure W) (c ≫ finiteGlobalStructure hπ data 1 hn)
        (integralSmoothStructure W) (finiteGlobalStructure hπ data 1 hn)
        (𝟙 _) c (𝟙 _) (by simp only [Category.comp_id, Category.id_comp])
        (Category.comp_id _) := by
    apply pullback.hom_ext <;> simp only [firstFractionInput, pullback.lift_fst,
      pullback.lift_snd, pullback.map, pullback.lift_fst, Category.comp_id]
  rw [he]
  exact MorphismProperty.pullbackMap (P := @IsOpenImmersion)
    (inferInstance : IsOpenImmersion (𝟙 _))
    (inferInstance : IsOpenImmersion c) (Category.id_comp _).symm rfl

/-- The entire simultaneous domain embeds into the whole first-successor action source. -/
def firstFractionDomainInclusion : firstFractionDomain hπ data hn f hf ⟶
    finiteGlobalActionProduct hπ data 1 hn :=
  pullback.fst _ _ ≫ firstFractionInput hπ data hn f hf

instance firstFractionDomainInclusion_isOpenImmersion :
    IsOpenImmersion (firstFractionDomainInclusion hπ data hn f hf) := by
  unfold firstFractionDomainInclusion
  infer_instance

/-- Comparison with the full divided-output domain uses the genuine two projections. -/
def firstFractionToDividedOutput : firstFractionDomain hπ data hn f hf ⟶
    firstDividedOutputDomain hπ data hn :=
  pullback.map (firstFractionOutput hπ data hn f hf) v
    (firstActionOutput hπ data hn) v (firstFractionInput hπ data hn f hf) (𝟙 _) (𝟙 _)
    (Category.comp_id _) (by simp only [Category.comp_id, Category.id_comp])

instance firstFractionToDividedOutput_isOpenImmersion :
    IsOpenImmersion (firstFractionToDividedOutput hπ data hn f hf) := by
  exact MorphismProperty.pullbackMap (P := @IsOpenImmersion)
    (inferInstance : IsOpenImmersion (firstFractionInput hπ data hn f hf))
    (inferInstance : IsOpenImmersion (𝟙 _)) rfl (Category.id_comp _).symm

/-- The full divided-domain comparison retains the actual successor input. -/
@[reassoc] theorem firstFractionToDividedOutput_fst :
    firstFractionToDividedOutput hπ data hn f hf ≫ pullback.fst _ _ =
      firstFractionDomainInclusion hπ data hn f hf := by
  simp only [firstFractionToDividedOutput, pullback.map, pullback.lift_fst]
  rfl

/-- The comparison retains the entire normalized divided-output projection. -/
@[reassoc] theorem firstFractionToDividedOutput_snd :
    firstFractionToDividedOutput hπ data hn f hf ≫ pullback.snd _ _ =
      pullback.snd (firstFractionOutput hπ data hn f hf) v := by
  simp only [firstFractionToDividedOutput, pullback.map, pullback.lift_snd, Category.comp_id]

end FLT.Mazur.WeierstrassDividedDepth
