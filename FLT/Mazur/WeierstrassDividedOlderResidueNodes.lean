/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedOlderSuccessiveCharts
public import FLT.Mazur.WeierstrassDividedFiniteNodeComponents
public import FLT.Mazur.WeierstrassDividedFiniteNodeContractions

/-!
# Ordered node neighborhoods retained in later residue models

The same two ordered node neighborhoods remain actual open charts after
every available number of later steps. Their union is the full inverse image
of the retained older integral chart, with the original residue structure.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (D : SplitNodeDepth W π depth) (j : ℕ) (hj : j + 1 ≤ n)
  (r : ℕ) (hr : j + 1 + r ≤ n)
  (hk0 : 0 < start + j) (hk : 2 * (start + j + 1) ≤ depth)
open WeierstrassSuccessiveX
local notation "K" => ResidueField R
local notation "e" => data (Fin.mk (j + 1) (Nat.lt_succ_of_le hj))
local notation "N" => MiddleNodeOpen (residue R (Data.b6 e))
local notation "a" => residueMiddleFirstNodeChart D (start + j) hk0 hk
  (Data.b3 e) (Data.b4 e) (Data.b6 e) (Data.factor3 e) (Data.factor4 e)
local notation "b" => residueMiddleSecondNodeChart D (start + j) hk0 hk
  (Data.b3 e) (Data.b4 e) (Data.b6 e) (Data.factor3 e) (Data.factor4 e)
local notation "c" => olderSuccessiveTensorChart hπ data j hj r hr K
local notation "q" => Spec.map (CommRingCat.ofHom (algebraMap R K))

/-- The first ordered full node neighborhood in the actual finite residue model. -/
def olderResidueFirstNode : Spec (.of N) ⟶ finiteTensorModel hπ data K (j + 1 + r) hr :=
  a ≫ c

/-- The opposite ordered full node neighborhood in the same finite residue model. -/
def olderResidueSecondNode : Spec (.of N) ⟶ finiteTensorModel hπ data K (j + 1 + r) hr :=
  b ≫ c

instance olderResidueFirstNode_isOpenImmersion :
    IsOpenImmersion (olderResidueFirstNode hπ data D j hj r hr hk0 hk) :=
  inferInstanceAs (IsOpenImmersion (_ ≫ _))

instance olderResidueSecondNode_isOpenImmersion :
    IsOpenImmersion (olderResidueSecondNode hπ data D j hj r hr hk0 hk) :=
  inferInstanceAs (IsOpenImmersion (_ ≫ _))

/-- The two ordered node charts cover exactly the original successive atlas preimage. -/
theorem olderResidueNodes_range :
    Set.range (olderResidueFirstNode hπ data D j hj r hr hk0 hk) ∪
      Set.range (olderResidueSecondNode hπ data D j hj r hr hk0 hk) =
        (pullback.snd q (finiteStructure hπ data (j + 1 + r) hr)) ⁻¹'
          Set.range (olderSuccessiveChart hπ data j hj r hr) := by
  rw [← olderSuccessiveTensorChart_range]
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

/-- The first full finite node chart retains its residue-field structure. -/
@[reassoc] theorem olderResidueFirstNode_structure :
    olderResidueFirstNode hπ data D j hj r hr hk0 hk ≫ pullback.fst _ _ =
      Spec.map (CommRingCat.ofHom (algebraMap K N)) := by
  rw [olderResidueFirstNode, Category.assoc, olderSuccessiveTensorChart_structure]
  exact residueMiddleFirstNodeChart_structure D (start + j) hk0 hk
    (Data.b3 e) (Data.b4 e) (Data.b6 e) (Data.factor3 e) (Data.factor4 e)

/-- The opposite ordered finite node retains the same residue-field structure. -/
@[reassoc] theorem olderResidueSecondNode_structure :
    olderResidueSecondNode hπ data D j hj r hr hk0 hk ≫ pullback.fst _ _ =
      Spec.map (CommRingCat.ofHom (algebraMap K N)) := by
  rw [olderResidueSecondNode, Category.assoc, olderSuccessiveTensorChart_structure]
  exact residueMiddleSecondNodeChart_structure D (start + j) hk0 hk
    (Data.b3 e) (Data.b4 e) (Data.b6 e) (Data.factor3 e) (Data.factor4 e)

local notation "d" => data (Fin.mk j (Nat.lt_succ_of_le (Nat.le_of_succ_le hj)))

/-- Later modifications retain the full original contraction of the first ordered node. -/
@[reassoc] theorem olderResidueFirstNode_toCurve :
    olderResidueFirstNode hπ data D j hj r hr hk0 hk ≫
      pullback.snd q (finiteStructure hπ data (j + 1 + r) hr) ≫
        finiteToCurve hπ data (j + 1 + r) hr =
      Spec.map (CommRingCat.ofHom
        (finiteFirstNodeContraction hπ data D j hj hk0 hk).toRingHom) ≫ toCurve d := by
  have h := finiteResidueFirstNode_toCurve hπ data D j hj hk0 hk
  rw [finiteResidueFirstNode, Category.assoc, finiteSuccessiveTensorChart_toCurve] at h
  rw [olderResidueFirstNode, Category.assoc, olderSuccessiveTensorChart_toCurve]
  exact h

/-- The opposite ordered node retains its full opposite-tangent contraction at every later stage. -/
@[reassoc] theorem olderResidueSecondNode_toCurve :
    olderResidueSecondNode hπ data D j hj r hr hk0 hk ≫
      pullback.snd q (finiteStructure hπ data (j + 1 + r) hr) ≫
        finiteToCurve hπ data (j + 1 + r) hr =
      Spec.map (CommRingCat.ofHom
        (finiteSecondNodeContraction hπ data D j hj hk0 hk).toRingHom) ≫ toCurve d := by
  have h := finiteResidueSecondNode_toCurve hπ data D j hj hk0 hk
  rw [finiteResidueSecondNode, Category.assoc, finiteSuccessiveTensorChart_toCurve] at h
  rw [olderResidueSecondNode, Category.assoc, olderSuccessiveTensorChart_toCurve]
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

/-- The first actual finite node retains the conic component as the u-zero branch. -/
theorem olderResidueFirstNode_conicLocus :
    olderResidueFirstNode hπ data D j hj r hr hk0 hk ⁻¹'
      (c '' PrimeSpectrum.zeroLocus (Ideal.span {u} : Set T)) =
        PrimeSpectrum.zeroLocus (Ideal.span {middleNodeU c₀} : Set (MiddleNodeOpen c₀)) := by
  rw [olderResidueFirstNode, residueMiddleFirstNodeChart_eq_spec,
    SpecChartIdeal.preimage_image_zeroLocus, residueFirstNodeMap_conicIdeal]

/-- The opposite actual finite node retains the same conic as its u-zero branch. -/
theorem olderResidueSecondNode_conicLocus :
    olderResidueSecondNode hπ data D j hj r hr hk0 hk ⁻¹'
      (c '' PrimeSpectrum.zeroLocus (Ideal.span {u} : Set T)) =
        PrimeSpectrum.zeroLocus (Ideal.span {middleNodeU c₀} : Set (MiddleNodeOpen c₀)) := by
  rw [olderResidueSecondNode, residueMiddleSecondNodeChart_eq_spec,
    SpecChartIdeal.preimage_image_zeroLocus, residueSecondNodeMap_conicIdeal]

/-- The zero-slope tensor line retains its ordered attachment inside the finite atlas. -/
theorem olderResidueFirstNode_lineLocus :
    olderResidueFirstNode hπ data D j hj r hr hk0 hk ⁻¹'
      (c '' PrimeSpectrum.zeroLocus (Ideal.span {t, v} : Set T)) =
        PrimeSpectrum.zeroLocus (Ideal.span {middleNodeZ c₀} : Set (MiddleNodeOpen c₀)) := by
  rw [olderResidueFirstNode, residueMiddleFirstNodeChart_eq_spec,
    SpecChartIdeal.preimage_image_zeroLocus, residueFirstNodeMap_lineIdeal]

/-- The opposite-slope tensor line retains the other ordered attachment in the finite atlas. -/
theorem olderResidueSecondNode_lineLocus :
    olderResidueSecondNode hπ data D j hj r hr hk0 hk ⁻¹'
      (c '' PrimeSpectrum.zeroLocus
        (Ideal.span {t, v + algebraMap K T (residue R W.a₁)} : Set T)) =
          PrimeSpectrum.zeroLocus (Ideal.span {middleNodeZ c₀} : Set (MiddleNodeOpen c₀)) := by
  rw [olderResidueSecondNode, residueMiddleSecondNodeChart_eq_spec,
    SpecChartIdeal.preimage_image_zeroLocus]
  exact congrArg (fun I : Ideal (MiddleNodeOpen c₀) =>
    PrimeSpectrum.zeroLocus (I : Set (MiddleNodeOpen c₀)))
    (residueSecondNodeMap_lineIdeal D (start + j) hk0 hk
      (Data.b3 e) (Data.b4 e) (Data.b6 e) (Data.factor3 e) (Data.factor4 e))

end FLT.Mazur.WeierstrassDividedDepth
