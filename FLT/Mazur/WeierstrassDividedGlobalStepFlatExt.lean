/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedGlobalStepExterior
public import FLT.Mazur.WeierstrassDividedGlobalSuccessiveCover
public import FLT.Mazur.WeierstrassGlobalModificationContractionFlatExt

/-!
# Flat reference uniqueness for every finite global step

Pull back the actual successor atlas along a flat reference map. The
unchanged branches and regular fraction denominators separate every
competitor, with no flatness assumption on that competitor.
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
  (data : (i : Fin (n + 1)) → Data W π (start + i.val)) (j : ℕ) (hj : j + 1 ≤ n)
local notation "d" => data (Fin.mk j (Nat.lt_succ_of_le (Nat.le_of_succ_le hj)))
local notation "e" => data (Fin.mk (j + 1) (Nat.lt_succ_of_le hj))
local notation "E" => finiteExterior hπ data
  (initialExterior (data (Fin.mk 0 (Nat.zero_lt_succ n)))) j (Nat.le_of_succ_le hj)
local notation "B" => WeierstrassDilatation.Coordinate W (π ^ (start + j))
  (π * (Data.b3 e)) (π * (Data.b4 e)) (π ^ 2 * (Data.b6 e))
local notation "I" => WeierstrassSuccessiveX.modificationCenter W (π ^ (start + j)) π
  (Data.b3 e) (Data.b4 e) (Data.b6 e)

local notation "g" => WeierstrassSuccessiveRees.centerGenerators W (π ^ (start + j)) π
  (Data.b3 e) (Data.b4 e) (Data.b6 e)
local notation "hg" => WeierstrassSuccessiveRees.centerGenerators_mem W (π ^ (start + j)) π
  (Data.b3 e) (Data.b4 e) (Data.b6 e)
/-- Flat affine maps into every actual successor chart have unique step lifts. -/
theorem finiteSuccessiveAtlas_flat_lift_ext (i : Option (Option (Fin 3)))
    {S : Type u} [CommRing S]
    (p : Spec (.of S) ⟶ finiteSuccessiveAtlasObject hπ data j hj i) [Flat p]
    (b : Spec (.of S) ⟶ finiteGlobalModel hπ data (j + 1) hj)
    (hb : b ≫ finiteGlobalStep hπ data j hj =
      p ≫ finiteSuccessiveAtlasMap hπ data j hj i ≫ finiteGlobalStep hπ data j hj) :
    b = p ≫ finiteSuccessiveAtlasMap hπ data j hj i := by
  rcases i with _ | (_ | i)
  · dsimp only [finiteSuccessiveAtlasMap] at hb ⊢
    rw [finiteGlobalStep_infinity] at hb
    let H := finiteGlobalStep_infinity_isPullback hπ data j hj
    have hd := H.lift_fst p b hb.symm
    have he := H.lift_snd p b hb.symm
    simp only [Category.comp_id] at hd
    rw [hd] at he
    exact he.symm
  · dsimp only [finiteSuccessiveAtlasMap] at hb ⊢
    rw [finiteSuccessiveRetainedChart_step] at hb
    let H := finiteGlobalStep_exterior_isPullback hπ data j hj
    have hd := H.lift_fst p b hb.symm
    have he := H.lift_snd p b hb.symm
    simp only [Category.comp_id] at hd
    rw [hd] at he
    exact he.symm
  · let ψ := affineChartRingHom p
    have hp : Spec.map (CommRingCat.ofHom ψ) = p := affineChartRingHom_spec p
    have hflat : ψ.Flat := by
      apply (Flat.SpecMap_iff (f := CommRingCat.ofHom ψ)).mp
      rw [hp]
      infer_instance
    let φ := ψ.comp (algebraMap B (BlowupFractionChart.chart I (g i)))
    have hI : (I).map φ = Ideal.span {ψ (BlowupFractionChart.denominator I (g i))} :=
      BlowupFractionChart.center_map_eq_mapped_denominator I (g i) (hg i) ψ
    have hd : IsRegular (ψ (BlowupFractionChart.denominator I (g i))) :=
      flatRingHom_isRegular ψ hflat (BlowupFractionChart.denominator_regular I (g i))
    have hc : (p ≫ finiteSuccessiveAtlasMap hπ data j hj (some (some i))) ≫
        finiteGlobalStep hπ data j hj =
          Spec.map (CommRingCat.ofHom φ) ≫ finiteNormalizedChart hπ data j hj := by
      rw [Category.assoc]
      change p ≫ finiteSuccessiveFractionChart hπ data j hj (g i) (hg i) ≫ _ = _
      rw [finiteSuccessiveFractionChart_step]
      change _ = Spec.map (CommRingCat.ofHom (ψ.comp (algebraMap B _))) ≫ _
      rw [CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc, hp]
    apply finiteGlobalStep_regular_center_ext hπ data j hj φ _ hI hd b
      (p ≫ finiteSuccessiveAtlasMap hπ data j hj (some (some i)))
    · exact hb.trans ((Category.assoc _ _ _).symm.trans hc)
    · exact hc

/-- Step contraction detects any competitor of a flat map into the entire successor. -/
theorem finiteGlobalStep_ext_of_flat {T : Scheme.{u}}
    (p : T ⟶ finiteGlobalModel hπ data (j + 1) hj) [Flat p]
    (b : T ⟶ finiteGlobalModel hπ data (j + 1) hj)
    (hb : b ≫ finiteGlobalStep hπ data j hj = p ≫ finiteGlobalStep hπ data j hj) :
    b = p := by
  let C := finiteSuccessiveOpenCover hπ data j hj
  let D := C.pullback₁ p
  apply Scheme.Cover.hom_ext D
  intro i
  apply (D.X i).affineCover.hom_ext
  intro k
  let q := (D.X i).affineCover.f k ≫ C.pullbackHom p i
  have hq : Flat q := by dsimp [q, Scheme.Cover.pullbackHom]; infer_instance
  let _ := hq
  have he : q ≫ C.f i = (D.X i).affineCover.f k ≫ D.f i ≫ p := by
    dsimp only [q]
    rw [Category.assoc, Scheme.Cover.pullbackHom_map]
  have hh := finiteSuccessiveAtlas_flat_lift_ext hπ data j hj i q
    ((D.X i).affineCover.f k ≫ D.f i ≫ b) (by
      change _ = q ≫ C.f i ≫ finiteGlobalStep hπ data j hj
      rw [← Category.assoc q, he]
      simp only [Category.assoc, hb])
  exact hh.trans he

end FLT.Mazur.WeierstrassDividedDepth
