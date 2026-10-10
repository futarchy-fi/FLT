/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedGlobalTensorCharts
public import FLT.Mazur.WeierstrassDividedFiniteNodeComponents
public import FLT.Mazur.WeierstrassDividedFiniteNodeContractions

/-!
# Ordered node neighborhoods in the global residue model

The same two ordered node neighborhoods remain actual open charts after
embedding in the projective model. Their union is the whole successive tensor
chart, with the original residue structure and ordered component loci.
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
  (hk0 : 0 < start + j) (hk : 2 * (start + j + 1) ≤ depth)
open WeierstrassSuccessiveX
local notation "K" => ResidueField R
local notation "e" => data (Fin.mk (j + 1) (Nat.lt_succ_of_le hj))
local notation "N" => MiddleNodeOpen (residue R (Data.b6 e))
local notation "a" => residueMiddleFirstNodeChart D (start + j) hk0 hk
  (Data.b3 e) (Data.b4 e) (Data.b6 e) (Data.factor3 e) (Data.factor4 e)
local notation "b" => residueMiddleSecondNodeChart D (start + j) hk0 hk
  (Data.b3 e) (Data.b4 e) (Data.b6 e) (Data.factor3 e) (Data.factor4 e)
local notation "c" => globalSuccessiveTensorChart hπ data K j hj
local notation "q" => Spec.map (CommRingCat.ofHom (algebraMap R K))

/-- The first ordered full node neighborhood in the actual global residue model. -/
def globalResidueFirstNode : Spec (.of N) ⟶ finiteGlobalTensorModel hπ data K (j + 1) hj :=
  a ≫ c

/-- The opposite ordered full node neighborhood in the same global residue model. -/
def globalResidueSecondNode : Spec (.of N) ⟶ finiteGlobalTensorModel hπ data K (j + 1) hj :=
  b ≫ c

instance globalResidueFirstNode_isOpenImmersion :
    IsOpenImmersion (globalResidueFirstNode hπ data D j hj hk0 hk) :=
  inferInstanceAs (IsOpenImmersion (_ ≫ _))

instance globalResidueSecondNode_isOpenImmersion :
    IsOpenImmersion (globalResidueSecondNode hπ data D j hj hk0 hk) :=
  inferInstanceAs (IsOpenImmersion (_ ≫ _))

/-- The two ordered node charts cover the entire global successive tensor chart. -/
theorem globalResidueNodes_range :
    Set.range (globalResidueFirstNode hπ data D j hj hk0 hk) ∪
      Set.range (globalResidueSecondNode hπ data D j hj hk0 hk) =
        Set.range c := by
  ext z
  constructor
  · rintro (⟨p, rfl⟩ | ⟨p, rfl⟩)
    · exact ⟨a p, rfl⟩
    · exact ⟨b p, rfl⟩
  · rintro ⟨p, rfl⟩
    rcases residueMiddleNodeCharts_cover D (start + j) hk0 hk
      (Data.b3 e) (Data.b4 e) (Data.b6 e) (Data.factor3 e) (Data.factor4 e) p with
      ⟨t, rfl⟩ | ⟨t, rfl⟩
    · exact Or.inl ⟨t, rfl⟩
    · exact Or.inr ⟨t, rfl⟩

/-- The first full global node chart retains its residue-field structure. -/
@[reassoc] theorem globalResidueFirstNode_structure :
    globalResidueFirstNode hπ data D j hj hk0 hk ≫ pullback.fst _ _ =
      Spec.map (CommRingCat.ofHom (algebraMap K N)) := by
  rw [globalResidueFirstNode, Category.assoc, globalSuccessiveTensorChart_structure]
  exact residueMiddleFirstNodeChart_structure D (start + j) hk0 hk
    (Data.b3 e) (Data.b4 e) (Data.b6 e) (Data.factor3 e) (Data.factor4 e)

/-- The opposite ordered global node retains the same residue-field structure. -/
@[reassoc] theorem globalResidueSecondNode_structure :
    globalResidueSecondNode hπ data D j hj hk0 hk ≫ pullback.fst _ _ =
      Spec.map (CommRingCat.ofHom (algebraMap K N)) := by
  rw [globalResidueSecondNode, Category.assoc, globalSuccessiveTensorChart_structure]
  exact residueMiddleSecondNodeChart_structure D (start + j) hk0 hk
    (Data.b3 e) (Data.b4 e) (Data.b6 e) (Data.factor3 e) (Data.factor4 e)

local notation "d" => data (Fin.mk j (Nat.lt_succ_of_le (Nat.le_of_succ_le hj)))

/-- The global embedding retains the full original contraction of the first ordered node. -/
@[reassoc] theorem globalResidueFirstNode_toCurve :
    globalResidueFirstNode hπ data D j hj hk0 hk ≫
      pullback.snd q (finiteGlobalStructure hπ data (j + 1) hj) ≫
        finiteGlobalContraction hπ data (j + 1) hj =
      Spec.map (CommRingCat.ofHom
        (finiteFirstNodeContraction hπ data D j hj hk0 hk).toRingHom) ≫ toCurve d := by
  have h := finiteResidueFirstNode_toCurve hπ data D j hj hk0 hk
  rw [finiteResidueFirstNode, Category.assoc, finiteSuccessiveTensorChart_toCurve] at h
  rw [globalResidueFirstNode, Category.assoc, globalSuccessiveTensorChart_toCurve]
  exact h

/-- The opposite node retains its full opposite-tangent contraction in the projective model. -/
@[reassoc] theorem globalResidueSecondNode_toCurve :
    globalResidueSecondNode hπ data D j hj hk0 hk ≫
      pullback.snd q (finiteGlobalStructure hπ data (j + 1) hj) ≫
        finiteGlobalContraction hπ data (j + 1) hj =
      Spec.map (CommRingCat.ofHom
        (finiteSecondNodeContraction hπ data D j hj hk0 hk).toRingHom) ≫ toCurve d := by
  have h := finiteResidueSecondNode_toCurve hπ data D j hj hk0 hk
  rw [finiteResidueSecondNode, Category.assoc, finiteSuccessiveTensorChart_toCurve] at h
  rw [globalResidueSecondNode, Category.assoc, globalSuccessiveTensorChart_toCurve]
  exact h

local notation "c₀" => residue R (Data.b6 e)
local notation "T" => ScalarExtension W (π ^ (start + j)) π
  (Data.b3 e) (Data.b4 e) (Data.b6 e) K
local notation "t" => tensorCoord W (π ^ (start + j)) π
  (Data.b3 e) (Data.b4 e) (Data.b6 e) K 0
local notation "v" => tensorCoord W (π ^ (start + j)) π
  (Data.b3 e) (Data.b4 e) (Data.b6 e) K 1
local notation "u" => tensorCoord W (π ^ (start + j)) π
  (Data.b3 e) (Data.b4 e) (Data.b6 e) K 2

/-- The first actual global node retains the conic component as the u-zero branch. -/
theorem globalResidueFirstNode_conicLocus :
    globalResidueFirstNode hπ data D j hj hk0 hk ⁻¹'
      (c '' PrimeSpectrum.zeroLocus (Ideal.span {u} : Set T)) =
        PrimeSpectrum.zeroLocus (Ideal.span {middleNodeU c₀} : Set (MiddleNodeOpen c₀)) := by
  rw [globalResidueFirstNode, residueMiddleFirstNodeChart_eq_spec,
    SpecChartIdeal.preimage_image_zeroLocus, residueFirstNodeMap_conicIdeal]

/-- The opposite actual global node retains the same conic as its u-zero branch. -/
theorem globalResidueSecondNode_conicLocus :
    globalResidueSecondNode hπ data D j hj hk0 hk ⁻¹'
      (c '' PrimeSpectrum.zeroLocus (Ideal.span {u} : Set T)) =
        PrimeSpectrum.zeroLocus (Ideal.span {middleNodeU c₀} : Set (MiddleNodeOpen c₀)) := by
  rw [globalResidueSecondNode, residueMiddleSecondNodeChart_eq_spec,
    SpecChartIdeal.preimage_image_zeroLocus, residueSecondNodeMap_conicIdeal]

/-- The zero-slope tensor line retains its ordered attachment inside the global atlas. -/
theorem globalResidueFirstNode_lineLocus :
    globalResidueFirstNode hπ data D j hj hk0 hk ⁻¹'
      (c '' PrimeSpectrum.zeroLocus (Ideal.span {t, v} : Set T)) =
        PrimeSpectrum.zeroLocus (Ideal.span {middleNodeZ c₀} : Set (MiddleNodeOpen c₀)) := by
  rw [globalResidueFirstNode, residueMiddleFirstNodeChart_eq_spec,
    SpecChartIdeal.preimage_image_zeroLocus, residueFirstNodeMap_lineIdeal]

/-- The opposite-slope tensor line retains the other ordered attachment in the global atlas. -/
theorem globalResidueSecondNode_lineLocus :
    globalResidueSecondNode hπ data D j hj hk0 hk ⁻¹'
      (c '' PrimeSpectrum.zeroLocus
        (Ideal.span {t, v + algebraMap K T (residue R W.a₁)} : Set T)) =
          PrimeSpectrum.zeroLocus (Ideal.span {middleNodeZ c₀} : Set (MiddleNodeOpen c₀)) := by
  rw [globalResidueSecondNode, residueMiddleSecondNodeChart_eq_spec,
    SpecChartIdeal.preimage_image_zeroLocus]
  exact congrArg (fun I : Ideal (MiddleNodeOpen c₀) =>
    PrimeSpectrum.zeroLocus (I : Set (MiddleNodeOpen c₀)))
    (residueSecondNodeMap_lineIdeal D (start + j) hk0 hk
      (Data.b3 e) (Data.b4 e) (Data.b6 e) (Data.factor3 e) (Data.factor4 e))

end FLT.Mazur.WeierstrassDividedDepth
