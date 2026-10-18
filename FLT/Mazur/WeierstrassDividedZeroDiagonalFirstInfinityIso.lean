/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedZeroDiagonalFirstInfinityComparison
public import FLT.Mazur.WeierstrassDividedArithmeticAffinePolygonEmbedding

/-!
# The actual first initial/infinity source union is a whole target node

The exact puncture preimage proves that gluing introduces no additional
identifications. The constructed surjective node map is an open immersion,
hence an isomorphism, at every original arithmetic order.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX
open WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] finiteGlobalModel finiteGlobalContraction
  arithmeticZeroFiniteInitialIso arithmeticInitialFactorRatioChart
  arithmeticZeroFiniteAtlasIso arithmeticZeroDiagonalInitialOpenIso
  arithmeticZeroDiagonalInitialTotalNodeIso arithmeticZeroDiagonalInfinityParameterIso
/-- Exact puncture preimages survive both full isomorphisms and an open target inclusion. -/
theorem factorRatioIsoTransport_preimage {A A' B O X X' Y : Scheme}
    (e : A ≅ A') (t : X ≅ X') (f : A ⟶ X) (g : B ⟶ X) (c : X' ⟶ Y)
    [IsOpenImmersion c] (p : O ⟶ A) (h : f ⁻¹' Set.range g = Set.range p) :
    (e.inv ≫ f ≫ t.hom ≫ c) ⁻¹' Set.range (g ≫ t.hom ≫ c) =
      Set.range (p ≫ e.hom) := by
  ext x
  obtain ⟨z, rfl⟩ := e.hom.homeomorph.surjective x
  have hf : (e.inv ≫ f ≫ t.hom ≫ c) (e.hom z) = c (t.hom (f z)) :=
    congrArg (fun k ↦ k z) (e.hom_inv_id_assoc (f ≫ t.hom ≫ c))
  change (e.inv ≫ f ≫ t.hom ≫ c) (e.hom z) ∈ Set.range (g ≫ t.hom ≫ c) ↔ _
  rw [hf]
  change (∃ a, c (t.hom (g a)) = c (t.hom (f z))) ↔ ∃ a, e.hom (p a) = e.hom z
  have ht : Function.Injective t.hom := t.hom.homeomorph.injective
  have he : Function.Injective e.hom := e.hom.homeomorph.injective
  simp only [c.isOpenEmbedding.injective.eq_iff, ht.eq_iff, he.eq_iff]
  exact Set.ext_iff.mp h z

variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R] {W : WeierstrassCurve R} {π : R}
  (hπ : π ≠ 0) {n : ℕ} (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (m : ℕ) (hj : 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "Q" => Quotient R π m
local notation "D" => arithmeticZeroDiagonalState hπ data H 0 hj u hu
local notation "s" => PolygonArithmeticSimultaneous.State.initial D m false
local notation "τ" => arithmeticInitialMobiusSmoothing W H.a1_unit (π ^ 1) π m
local notation "l" => arithmeticZeroDiagonalInitialOverlap hπ data H m hj u hu false
local notation "i" => arithmeticZeroDiagonalOverlapToInfinity hπ data H m hj u hu
local notation "F" => arithmeticZeroDiagonalInitialFactorRatio hπ data H m hj u hu false
local notation "C" => arithmeticZeroDiagonalPolygonInitialMap hπ data H m hj u hu false
local notation "f" => arithmeticZeroDiagonalFactorRatioInitialMap hπ data H m hj u hu false
local notation "g" => arithmeticZeroDiagonalFactorRatioInfinityMap hπ data H m hj u hu
local notation "E" => arithmeticZeroDiagonalInfinityParameterIso hπ data H m hj u hu
local notation "T" => arithmeticZeroDiagonalInitialTotalNodeIso hπ data H m hj u hu false
local notation "v" => Iso.hom E ≫ rightBranchOpen Q τ ≫ Iso.hom T
local notation "U" => arithmeticZeroDiagonalFirstInfinityUnionIso hπ data H m hj u hu

local notation "d" => data (Fin.mk 0 (Nat.zero_lt_succ n))
local notation "N₀" => arithmeticInitialFactorRatioChart π m W (π ^ 1)
  (Data.b3 d) (Data.b4 d) (Data.b6 d) H.a1_unit H.a2_div
    (H.b3_div _) (H.b4_div _) (H.b6_div _)
local notation "P" => polynomialNodeOverlapInclusion (W.map (algebraMap R Q))
  (algebraMap R Q (π ^ 1))
local notation "S" => arithmeticZeroDiagonalInitialOpenIso hπ data H m hj u hu false
local notation "B" => arithmeticZeroDiagonalInitialInfinityBoundary hπ data H m hj u hu false
local notation "N" => arithmeticZeroDiagonalFirstInfinityNodeMap hπ data H m hj u hu
local notation "V" => arithmeticZeroDiagonalFirstInfinityUnionNodeMap hπ data H m hj u hu

omit [IsBezout R] in
/-- The full infinity image pulls back to exactly the actual original first D(q). -/
theorem arithmeticZeroDiagonalFirstInfinity_preimage :
    f ⁻¹' Set.range g = Set.range l := by
  rw [arithmeticZeroDiagonalFactorRatioInfinityMap_range hπ data H m hj u hu false]
  simp only [arithmeticZeroDiagonalFactorRatioInitialMap,
    arithmeticZeroDiagonalInitialFactorRatio, arithmeticZeroDiagonalInitialInfinityBoundary,
    arithmeticZeroDiagonalInitialOverlap, Bool.false_eq_true, ↓reduceIte, Category.assoc]
  rw [show (arithmeticZeroFiniteAtlasIso hπ data H m m hj u hu (.initial false)).hom =
    (S).hom from by unfold arithmeticZeroDiagonalInitialOpenIso; rfl]
  exact factorRatioIsoTransport_preimage S T N₀ (rightBranchOpen Q τ) C P
      (arithmeticInitialFactorRatioChart_right_preimage π m W (π ^ 1)
        (Data.b3 d) (Data.b4 d) (Data.b6 d) H.a1_unit H.a2_div
          (H.b3_div _) (H.b4_div _) (H.b6_div _))

/-- The target first initial/infinity maps have the full original source intersection. -/
theorem arithmeticZeroDiagonalFirstInfinity_comparison_isPullback :
    IsPullback i l g f := by
  apply IsOpenImmersion.isPullback _ _ _ _
    (arithmeticZeroDiagonalFactorRatioInfinityMap_overlap_first hπ data H m hj u hu).symm
  exact TopologicalSpace.Opens.ext
    (arithmeticZeroDiagonalFirstInfinity_preimage hπ data H m hj u hu)

/-- The glued complete node map introduces no extra identifications or local functions. -/
instance arithmeticZeroDiagonalFirstInfinityNodeMap_isOpenImmersion : IsOpenImmersion N := by
  have he : N ≫ C = pushout.desc g f
      (arithmeticZeroDiagonalFactorRatioInfinityMap_overlap_first hπ data H m hj u hu) := by
    apply pushout.hom_ext
    · rw [arithmeticZeroDiagonalFirstInfinityNodeMap_infinity_polygon,
        pushout.inl_desc]
    · rw [arithmeticZeroDiagonalFirstInfinityNodeMap_initial_polygon,
        pushout.inr_desc]
  let _ : IsOpenImmersion (N ≫ C) := by
    rw [he]
    exact SchemeOpenPushout.coverDesc_isOpenImmersion i l g f
      (arithmeticZeroDiagonalFirstInfinity_comparison_isPullback hπ data H m hj u hu)
  exact IsOpenImmersion.of_comp N C

instance arithmeticZeroDiagonalFirstInfinityNodeMap_isIso : IsIso N := by
  apply isIso_of_isOpenImmersion_of_opensRange_eq_top
  exact TopologicalSpace.Opens.ext
    (Set.range_eq_univ.mpr
      (arithmeticZeroDiagonalFirstInfinityNodeMap_surjective hπ data H m hj u hu))

instance arithmeticZeroDiagonalFirstInfinityUnionNodeMap_isIso : IsIso V := by
  unfold arithmeticZeroDiagonalFirstInfinityUnionNodeMap
  infer_instance

/-- The actual full first source union is isomorphic to its independently constructed node. -/
def arithmeticZeroDiagonalFirstInfinityUnionNodeIso :
    (arithmeticZeroDiagonalFirstInfinityUnion hπ data H m hj u hu).toScheme ≅
      PolygonSmoothing.chart Q s := asIso V

/-- The isomorphism retains the already constructed full source-union comparison. -/
theorem arithmeticZeroDiagonalFirstInfinityUnionNodeIso_hom :
    (arithmeticZeroDiagonalFirstInfinityUnionNodeIso hπ data H m hj u hu).hom = V := rfl

instance arithmeticZeroDiagonalFirstInfinityUnionComparison_isOpenImmersion :
    IsOpenImmersion (arithmeticZeroDiagonalFirstInfinityUnionComparison hπ data H m hj u hu) := by
  unfold arithmeticZeroDiagonalFirstInfinityUnionComparison
  infer_instance

end FLT.Mazur.WeierstrassDividedDepth
