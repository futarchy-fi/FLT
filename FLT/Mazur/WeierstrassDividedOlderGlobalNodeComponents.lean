/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedOlderGlobalResidueNodes

/-!
# Ordered component loci retained by the older global nodes

Global open embedding preserves the exact conic and ordered line loci
already proved for the finite older nodes. No new residue comparison is used.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (D : SplitNodeDepth W π depth) (j : ℕ) (hj : j + 1 ≤ n)
  (r : ℕ) (hr : j + 1 + r ≤ n)
  (hk0 : 0 < start + j) (hk : 2 * (start + j + 1) ≤ depth)
open WeierstrassSuccessiveX
local notation "K" => ResidueField R
local notation "e" => data (Fin.mk (j + 1) (Nat.lt_succ_of_le hj))
local notation "d" => data (Fin.mk j (Nat.lt_succ_of_le (Nat.le_of_succ_le hj)))
local notation "N" => MiddleNodeOpen (residue R (Data.b6 e))
local notation "g" => finiteLocalTensorEmbedding hπ data K (j + 1 + r) hr
local notation "q" => Spec.map (CommRingCat.ofHom (algebraMap R K))


/-- An ambient open embedding preserves the inverse image of every chart subset. -/
theorem olderGlobalNode_preimage_image {A B X Y : Scheme.{u}}
    (a : A ⟶ X) (b : B ⟶ X) (emb : X ⟶ Y) [IsOpenImmersion emb] (Z : Set B) :
    (a ≫ emb) ⁻¹' ((b ≫ emb) '' Z) = a ⁻¹' (b '' Z) := by
  change (emb ∘ a) ⁻¹' ((emb ∘ b) '' Z) = _
  rw [Set.image_comp, Set.preimage_comp,
    Set.preimage_image_eq _ emb.isOpenEmbedding.injective]

local notation "c₀" => residue R (Data.b6 e)
local notation "T" => ScalarExtension W (π ^ (start + j)) π
  (Data.b3 e) (Data.b4 e) (Data.b6 e) K
local notation "t" => tensorCoord W (π ^ (start + j)) π
  (Data.b3 e) (Data.b4 e) (Data.b6 e) K 0
local notation "v" => tensorCoord W (π ^ (start + j)) π
  (Data.b3 e) (Data.b4 e) (Data.b6 e) K 1
local notation "u" => tensorCoord W (π ^ (start + j)) π
  (Data.b3 e) (Data.b4 e) (Data.b6 e) K 2
local notation "c" => olderGlobalTensorChart hπ data K j hj r hr

/-- The older first node retains its ordered conic locus in the global model. -/
theorem olderGlobalResidueFirstNode_conicLocus :
    olderGlobalResidueFirstNode hπ data D j hj r hr hk0 hk ⁻¹'
      (c '' PrimeSpectrum.zeroLocus (Ideal.span {u} : Set T)) =
        PrimeSpectrum.zeroLocus (Ideal.span {middleNodeU c₀} : Set (MiddleNodeOpen c₀)) := by
  rw [olderGlobalResidueFirstNode, olderGlobalTensorChart, olderGlobalNode_preimage_image]
  exact olderResidueFirstNode_conicLocus hπ data D j hj r hr hk0 hk

/-- The older second node retains its ordered conic locus in the global model. -/
theorem olderGlobalResidueSecondNode_conicLocus :
    olderGlobalResidueSecondNode hπ data D j hj r hr hk0 hk ⁻¹'
      (c '' PrimeSpectrum.zeroLocus (Ideal.span {u} : Set T)) =
        PrimeSpectrum.zeroLocus (Ideal.span {middleNodeU c₀} : Set (MiddleNodeOpen c₀)) := by
  rw [olderGlobalResidueSecondNode, olderGlobalTensorChart, olderGlobalNode_preimage_image]
  exact olderResidueSecondNode_conicLocus hπ data D j hj r hr hk0 hk

/-- The older first node retains its ordered line locus in the global model. -/
theorem olderGlobalResidueFirstNode_lineLocus :
    olderGlobalResidueFirstNode hπ data D j hj r hr hk0 hk ⁻¹'
      (c '' PrimeSpectrum.zeroLocus (Ideal.span {t, v} : Set T)) =
        PrimeSpectrum.zeroLocus (Ideal.span {middleNodeZ c₀} : Set (MiddleNodeOpen c₀)) := by
  rw [olderGlobalResidueFirstNode, olderGlobalTensorChart, olderGlobalNode_preimage_image]
  exact olderResidueFirstNode_lineLocus hπ data D j hj r hr hk0 hk

/-- The older second node retains its ordered line locus in the global model. -/
theorem olderGlobalResidueSecondNode_lineLocus :
    olderGlobalResidueSecondNode hπ data D j hj r hr hk0 hk ⁻¹'
      (c '' PrimeSpectrum.zeroLocus (Ideal.span {t, v + algebraMap K T (residue R W.a₁)} : Set T)) =
        PrimeSpectrum.zeroLocus (Ideal.span {middleNodeZ c₀} : Set (MiddleNodeOpen c₀)) := by
  rw [olderGlobalResidueSecondNode, olderGlobalTensorChart, olderGlobalNode_preimage_image]
  exact olderResidueSecondNode_lineLocus hπ data D j hj r hr hk0 hk

end FLT.Mazur.WeierstrassDividedDepth
