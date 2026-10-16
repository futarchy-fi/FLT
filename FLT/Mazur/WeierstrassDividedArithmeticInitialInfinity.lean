/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationXArithmeticNodeInfinity
public import FLT.Mazur.WeierstrassDividedArithmeticInitialNodeOverlap
public import FLT.Mazur.WeierstrassDividedInitialTensorInfinityIntersection

/-!
# Full arithmetic initial-node intersections with infinity

The common standard D(q) is the entire initial/infinity intersection, and
also the entire intersection of each full initial node with infinity.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
open scoped TensorProduct
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassModificationX PolygonArithmeticStages
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] finiteGlobalModel finiteGlobalContraction
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val)) (m : ℕ)
  (j : ℕ) (hj : j ≤ n)
local notation "Q" => Quotient R π m
local notation "d" => data (Fin.mk 0 (Nat.zero_lt_succ n))
variable (ha : IsUnit W.a₁) (h2 : π ∣ W.a₂)
  (h3 : π ∣ (data ⟨0, Nat.zero_lt_succ n⟩).b3)
  (h4 : π ∣ (data ⟨0, Nat.zero_lt_succ n⟩).b4)
  (h6 : π ∣ (data ⟨0, Nat.zero_lt_succ n⟩).b6)
local notation "F" => arithmeticInitialTensorNodeChart π m W (π ^ start)
  (Data.b3 d) (Data.b4 d) (Data.b6 d) ha h2 h3 h4 h6
local notation "G" => arithmeticOppositeInitialTensorNodeChart π m W (π ^ start)
  (Data.b3 d) (Data.b4 d) (Data.b6 d) ha h2 h3 h4 h6
local notation "c" => finiteArithmeticInitialTensorChart hπ data m j hj
local notation "P" => polynomialNodeOverlapInclusion
  (W.map (algebraMap R Q)) (algebraMap R Q (π ^ start))
local notation "B" => arithmeticNodeOverlapOpposite π m W (π ^ start)
  (Data.b3 d) (Data.b4 d) (Data.b6 d) ha h2 h3 h4 h6


local notation "q" => Spec.map (CommRingCat.ofHom (algebraMap R Q))
local notation "E" => pullbackSymmetry q (finiteGlobalStructure hπ data j hj)
local notation "i" => finiteInfinityTensorChart hπ data Q j hj ≫ Iso.hom E
local notation "Y" => WeierstrassModificationX.y W (π ^ start)
  (Data.b3 d) (Data.b4 d) (Data.b6 d)

omit [IsDomain R] [IsBezout R] in
/-- The full standard overlap maps to exactly the original arithmetic y-principal open. -/
theorem arithmeticInitialOverlap_range :
    Set.range (P ≫ F) = Set.range (PrincipalOpenTensor.inclusion Q Y) := by
  change Set.range (P ≫ F) = Set.range (PrimeSpectrum.comap
    (algebraMap _ (Localization.Away ((1 : Q) ⊗ₜ[R] Y))))
  rw [PrimeSpectrum.localization_away_comap_range _ ((1 : Q) ⊗ₜ[R] Y),
    arithmeticInitialTensorY_node_intersection π m W (π ^ start)
      (Data.b3 d) (Data.b4 d) (Data.b6 d) ha h2 h3 h4 h6]
  have H := arithmeticTensorNodes_isPullback π m W (π ^ start)
    (Data.b3 d) (Data.b4 d) (Data.b6 d) ha h2 h3 h4 h6
  ext z
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨⟨P x, rfl⟩, ⟨B x, congrArg (fun f => f x) H.w.symm⟩⟩
  · rintro ⟨⟨x, hx⟩, ⟨y, hy⟩⟩
    obtain ⟨w, hw, _⟩ := Scheme.exists_preimage_of_isPullback H x y (hx.trans hy.symm)
    exact ⟨w, (congrArg F hw).trans hx⟩

/-- The complete global arithmetic initial/infinity preimage is the full standard overlap. -/
theorem arithmeticInitial_infinity_preimage : c ⁻¹' Set.range i = Set.range (P ≫ F) := by
  rw [arithmeticInitialOverlap_range data m ha h2 h3 h4 h6]
  have he : c ⁻¹' Set.range i = (globalInitialTensorChart hπ data Q j hj) ⁻¹'
      Set.range (finiteInfinityTensorChart hπ data Q j hj) := by
    ext z
    constructor
    · rintro ⟨x, hx⟩
      exact ⟨x, (E).hom.homeomorph.injective hx⟩
    · rintro ⟨x, hx⟩
      exact ⟨x, congrArg (E).hom hx⟩
  rw [he]
  exact initialGlobalTensor_infinity_preimage hπ data Q j hj

/-- The complete initial standard overlap maps to the unchanged original infinity tensor chart. -/
def arithmeticInitialOverlapToInfinity :=
  IsOpenImmersion.lift i ((P ≫ F) ≫ c) (by
    rintro _ ⟨x, rfl⟩
    exact Set.ext_iff.mp (arithmeticInitial_infinity_preimage
      hπ data m j hj ha h2 h3 h4 h6) ((P ≫ F) x) |>.mpr ⟨x, rfl⟩)

/-- Both actual arithmetic chart restrictions agree on the entire standard overlap. -/
@[reassoc] theorem arithmeticInitialOverlapToInfinity_comp :
    arithmeticInitialOverlapToInfinity hπ data m j hj ha h2 h3 h4 h6 ≫ i = (P ≫ F) ≫ c :=
  IsOpenImmersion.lift_fac _ _ _

/-- The full standard overlap is the complete original initial-chart/infinity fiber product. -/
theorem arithmeticInitial_infinity_isPullback :
    IsPullback (arithmeticInitialOverlapToInfinity hπ data m j hj ha h2 h3 h4 h6)
      (P ≫ F) i c := by
  let _ := arithmeticInitialTensorNodeChart_isOpenImmersion π m W (π ^ start)
    (Data.b3 d) (Data.b4 d) (Data.b6 d) ha h2 h3 h4 h6
  apply IsOpenImmersion.isPullback
  · exact (arithmeticInitialOverlapToInfinity_comp hπ data m j hj ha h2 h3 h4 h6).symm
  · exact TopologicalSpace.Opens.ext
      (arithmeticInitial_infinity_preimage hπ data m j hj ha h2 h3 h4 h6)

/-- The first full initial node meets infinity in its exact complete standard D(q). -/
theorem arithmeticFirstNode_infinity_isPullback :
    IsPullback (arithmeticInitialOverlapToInfinity hπ data m j hj ha h2 h3 h4 h6)
      P i (F ≫ c) := by
  let _ := arithmeticInitialTensorNodeChart_isOpenImmersion π m W (π ^ start)
    (Data.b3 d) (Data.b4 d) (Data.b6 d) ha h2 h3 h4 h6
  have H : IsPullback (𝟙 _) P (P ≫ F) F :=
    IsPullback.of_horiz_isIso_mono ⟨by simp only [Category.id_comp]⟩
  simpa only [Category.id_comp] using H.paste_horiz
    (arithmeticInitial_infinity_isPullback hπ data m j hj ha h2 h3 h4 h6)

/-- The opposite full node has the same infinity overlap with its actual restriction. -/
theorem arithmeticOppositeNode_infinity_isPullback :
    IsPullback (arithmeticInitialOverlapToInfinity hπ data m j hj ha h2 h3 h4 h6)
      B i (G ≫ c) := by
  let _ := arithmeticOppositeInitialTensorNodeChart_isOpenImmersion π m W (π ^ start)
    (Data.b3 d) (Data.b4 d) (Data.b6 d) ha h2 h3 h4 h6
  have H := arithmeticInitial_infinity_isPullback hπ data m j hj ha h2 h3 h4 h6
  rw [arithmeticTensorNodes_overlap] at H
  have H' : IsPullback (𝟙 _) B (B ≫ G) G :=
    IsPullback.of_horiz_isIso_mono ⟨by simp only [Category.id_comp]⟩
  simpa only [Category.id_comp] using H'.paste_horiz H

end FLT.Mazur.WeierstrassDividedDepth
