/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassInfinityFactorRatioIso
public import FLT.Mazur.WeierstrassDividedRevisedTensorMaps

/-!
# The complete original infinity image in the revised polygon

At every arithmetic order the full original cubic embeds onto the entire
revised infinity edge. The original tensor chart has exactly the same image.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
section Full
variable {S : Type} [CommRing S] (V : WeierstrassCurve S) (ha : IsUnit V.a₁)
  (s τ b3 : S) (r : Polynomial S) (I : Ideal S) (hI : IsNilpotent I)
  (hr : r ∈ I.map Polynomial.C) (hb : b3 ∈ I)
  {Y : Scheme} (c : (b : Bool) → PolygonSmoothing.chart S τ ⟶ Y)
  (h2 : V.a₂ ∈ I) (h3 : V.a₃ ∈ I) (h4 : V.a₄ ∈ I) (h6 : V.a₆ ∈ I)
local notation "P" => infinityFactorRatioParameter V I hI h2 h3 h4 h6 s b3 r hr hb
local notation "F" => factorRatioInfinityTargetMap V s τ b3 r I hI hr hb c h2 h3 h4 h6

include ha in
/-- The full original infinity map embeds whenever its target node embeds. -/
theorem factorRatioInfinityTargetMap_isOpenImmersion [IsOpenImmersion (c false)] :
    IsOpenImmersion F := by
  let _ : IsIso P := infinityFactorRatioParameter_isIso V ha I hI h2 h3 h4 h6 s b3 r hr hb
  change IsOpenImmersion (P ≫ rightBranchOpen S τ ≫ c false)
  infer_instance

include ha in
/-- The actual infinity image is the entire target edge, with no residue restriction. -/
theorem factorRatioInfinityTargetMap_range :
    Set.range F = Set.range (rightBranchOpen S τ ≫ c false) := by
  have hs := infinityFactorRatioParameter_surjective V ha I hI h2 h3 h4 h6 s b3 r hr hb
  change Set.range ((rightBranchOpen S τ ≫ c false) ∘ P) = _
  rw [Set.range_comp, hs.range_eq, Set.image_univ]
end Full

variable {R : Type} [CommRing R] {W : WeierstrassCurve R} {π : R} {n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (m j : ℕ) (hj : j + 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "Q" => Quotient R π m
local notation "τ" => arithmeticInitialMobiusSmoothing W H.a1_unit (π ^ 1) π m
local notation "c" => arithmeticRevisedPolygonInitialChart data H m j hj u hu
local notation "F" => arithmeticOriginalRevisedInfinityMap data H m j hj u hu
local notation "G" => arithmeticOriginalRevisedTensorInfinityMap data H m j hj u hu

/-- The full original infinity chart embeds in the revised polygon at every order. -/
instance arithmeticOriginalRevisedInfinityMap_isOpenImmersion : IsOpenImmersion F := by
  unfold arithmeticOriginalRevisedInfinityMap
  apply factorRatioInfinityTargetMap_isOpenImmersion
    (ha := H.a1_unit.map (algebraMap R Q))

/-- The entire revised initial edge is filled by the original infinity chart. -/
theorem arithmeticOriginalRevisedInfinityMap_range :
    Set.range F = Set.range (rightBranchOpen Q τ ≫ c false) := by
  unfold arithmeticOriginalRevisedInfinityMap
  apply factorRatioInfinityTargetMap_range (ha := H.a1_unit.map (algebraMap R Q))

/-- Both oriented infinity edges have the same complete image in the revised target. -/
theorem arithmeticRevisedPolygon_infinity_range (b : Bool) :
    Set.range (rightBranchOpen Q τ ≫ (twistedRetainedOrientation data H m b).hom ≫ c b) =
      Set.range (rightBranchOpen Q τ ≫ c false) := by
  cases b
  · simp only [twistedRetainedOrientation, Bool.false_eq_true, ↓reduceIte,
      Iso.refl_hom, Category.id_comp]
  · rw [arithmeticRevisedPolygon_infinity]
    have hs : Function.Surjective (edgeInversion Q).hom :=
      (Scheme.homeoOfIso (edgeInversion Q)).surjective
    change Set.range ((rightBranchOpen Q τ ≫ c false) ∘ (edgeInversion Q).hom) = _
    rw [Set.range_comp, hs.range_eq, Set.image_univ]

/-- The original tensor infinity chart also embeds, before any chart replacement. -/
instance arithmeticOriginalRevisedTensorInfinityMap_isOpenImmersion : IsOpenImmersion G := by
  unfold arithmeticOriginalRevisedTensorInfinityMap
  infer_instance

/-- Tensor transport retains the entire infinity edge as the exact image. -/
theorem arithmeticOriginalRevisedTensorInfinityMap_range :
    Set.range G = Set.range (rightBranchOpen Q τ ≫ c false) := by
  have hs : Function.Surjective (arithmeticInfinityTensorIso π m W).inv :=
    (Scheme.homeoOfIso (arithmeticInfinityTensorIso π m W).symm).surjective
  change Set.range (F ∘ (arithmeticInfinityTensorIso π m W).inv) = _
  rw [Set.range_comp, hs.range_eq, Set.image_univ, arithmeticOriginalRevisedInfinityMap_range]

end FLT.Mazur.WeierstrassDividedDepth
