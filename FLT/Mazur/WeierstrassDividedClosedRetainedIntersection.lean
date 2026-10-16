/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedClosedInitialRetainedIntersection
public import FLT.Mazur.WeierstrassDividedRetainedChartOpen
public import FLT.Mazur.WeierstrassDividedRetainedPuncturePreimage
public import FLT.Mazur.WeierstrassDividedPolygonRetainedIntersection

/-!
# Reflection of all original retained intersections

Full corrected retained charts retain their exact puncture preimages.
The target classification and unchanged original adjacent squares therefore
reflect every retained/retained equality into the original global stage.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] finiteGlobalModel finiteGlobalContraction
  arithmeticRetainedFixedSmoothingIso
/-- Full puncture preimages transport retained intersection classification through corrections. -/
theorem retainedPolygon_intersection_transport (R : Type*) [CommRing R] (s t : R)
    [Fact (IsNilpotent t)] (k : ℕ)
    (C : Fin k → (PolygonSmoothing.chart R s ⟶ PolygonSmoothing.chart R t))
    (hp : ∀ i, C i ⁻¹' Set.range (leftBranchOpen R t) = Set.range (leftBranchOpen R s))
    (a d : Fin k) (b e : Bool) (x y : PolygonSmoothing.chart R s)
    (h : (C a ≫ retainedPolygonMap R t k a b) x =
      (C d ≫ retainedPolygonMap R t k d e) y) :
    (a = d ∧ b = e) ∨
      (a.val + 1 = d.val ∧ b = e ∧ x ∈ Set.range (leftBranchOpen R s)) ∨
      (d.val + 1 = a.val ∧ b = e ∧ y ∈ Set.range (leftBranchOpen R s)) := by
  rcases retainedPolygon_intersection R t k a d b e (C a x) (C d y) h with
    hs | ⟨hi, hb, hx⟩ | ⟨hi, hb, hy⟩
  · exact Or.inl hs
  · exact Or.inr (Or.inl ⟨hi, hb, (Set.ext_iff.mp (hp a) x).mp hx⟩)
  · exact Or.inr (Or.inr ⟨hi, hb, (Set.ext_iff.mp (hp d) y).mp hy⟩)

variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (j : ℕ) (hj : j + 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "Q" => Quotient R π 0
local notation "τ" => arithmeticInitialMobiusSmoothing W H.a1_unit (π ^ 1) π 0
local notation "hn" => Fact.mk
  (arithmeticInitialFactorRatioSmoothing_nilpotent W H.a1_unit (π ^ 1) π 0 H.scale_div)
local notation "a" => arithmeticLabeledAtlasMap hπ data H 0 (j + 1) hj
local notation "G" => arithmeticClosedPolygonComparisonChart hπ data H j hj u hu
local notation "C" => arithmeticRetainedFixedSmoothingIso data H 0 (j + 1) hj
local notation "l" => leftBranchOpen Q (parameter R π 0)
local notation "r" => precedingBranch Q (parameter R π 0)

omit [IsBezout R] in
/-- The actual retained comparison uses its full correction before the original orientation. -/
theorem arithmeticClosedRetained_corrected (idx : Fin (j + 1)) (b : Bool) :
    let _ := hn
    G (.retained idx b) = (C idx).hom ≫ retainedPolygonMap Q τ (j + 1) idx b := by
  let _ := hn
  exact arithmeticStartOneRetainedMap_factorization hπ data H 0 (j + 1) hj idx b

attribute [local irreducible] arithmeticClosedPolygonComparisonChart

omit [IsBezout R] in
/-- Every actual retained equality has its original label and full outgoing puncture. -/
theorem arithmeticClosedRetained_location (idx other : Fin (j + 1)) (b e : Bool)
    (x y : PolygonSmoothing.chart Q (parameter R π 0))
    (h : G (.retained idx b) x = G (.retained other e) y) :
    (idx = other ∧ b = e) ∨
      (idx.val + 1 = other.val ∧ b = e ∧ x ∈ Set.range l) ∨
      (other.val + 1 = idx.val ∧ b = e ∧ y ∈ Set.range l) := by
  let _ := hn
  have hx := congrArg (fun f ↦ f x)
    (arithmeticClosedRetained_corrected hπ data H j hj u hu idx b)
  have hy := congrArg (fun f ↦ f y)
    (arithmeticClosedRetained_corrected hπ data H j hj u hu other e)
  have he := hx.symm.trans (h.trans hy)
  exact retainedPolygon_intersection_transport Q (parameter R π 0) τ (j + 1)
    (fun idx ↦ (C idx).hom)
    (arithmeticRetainedFixedSmoothingIso_left_preimage data H 0 (j + 1) hj)
    idx other b e x y he

/-- The original adjacent square recovers source equality on the complete outgoing puncture. -/
theorem arithmeticClosedRetained_adjacent_points_eq (i : ℕ) (hi : i + 1 < j + 1) (b : Bool)
    (x y : PolygonSmoothing.chart Q (parameter R π 0)) (hx : x ∈ Set.range l)
    (h : G (.retained ⟨i, by omega⟩ b) x = G (.retained ⟨i + 1, hi⟩ b) y) :
    a (.retained ⟨i, by omega⟩ b) x = a (.retained ⟨i + 1, hi⟩ b) y := by
  exact fullChartOverlap_points_eq _ _ _ _ l r
    (arithmeticLabeledAtlas_adjacent_isPullback hπ data H 0 (j + 1) hj i hi b).w
    (arithmeticClosedPolygonComparisonChart_adjacent hπ data H j hj u hu i hi b)
    (G (.retained ⟨i + 1, hi⟩ b)).isOpenEmbedding.injective x y hx h

/-- All retained labels reflect equality, including both adjacent orientations and same labels. -/
theorem arithmeticClosedRetained_points_eq (idx other : Fin (j + 1)) (b e : Bool)
    (x y : PolygonSmoothing.chart Q (parameter R π 0))
    (h : G (.retained idx b) x = G (.retained other e) y) :
    a (.retained idx b) x = a (.retained other e) y := by
  rcases arithmeticClosedRetained_location hπ data H j hj u hu idx other b e x y h with
    ⟨rfl, rfl⟩ | ⟨hi, rfl, hx⟩ | ⟨hi, rfl, hy⟩
  · exact congrArg (a (.retained idx b)) ((G (.retained idx b)).isOpenEmbedding.injective h)
  · have hlt : idx.val + 1 < j + 1 := by omega
    have hd : other = ⟨idx.val + 1, hlt⟩ := Fin.ext hi.symm
    subst other
    exact arithmeticClosedRetained_adjacent_points_eq hπ data H j hj u hu
      idx.val hlt b x y hx h
  · have hlt : other.val + 1 < j + 1 := by omega
    have hd : idx = ⟨other.val + 1, hlt⟩ := Fin.ext hi.symm
    subst idx
    exact (arithmeticClosedRetained_adjacent_points_eq hπ data H j hj u hu
      other.val hlt b y x hy h.symm).symm

end FLT.Mazur.WeierstrassDividedDepth
