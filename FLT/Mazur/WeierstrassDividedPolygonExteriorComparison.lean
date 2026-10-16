/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedPolygonComparisonCharts
public import FLT.Mazur.OpenImmersionImageUnionGluing

/-!
# A polygon comparison on the entire original exterior

All nonterminal labels are glued over their actual global open union. Every
full pair intersection is checked, including the initial triangle, both first
edges and all retained depths. The terminal node is not removed from its own
chart and then silently treated as a completed global comparison.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] finiteGlobalModel finiteGlobalContraction

/-- Exactly the original labels other than the terminal chart. -/
abbrev ArithmeticExteriorLabel (k : ℕ) :=
  {i : ArithmeticChartLabel k // i ≠ .terminal}

variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (m j : ℕ) (hj : j + 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "c" => arithmeticLabeledAtlasMap hπ data H m (j + 1) hj
local notation "F" => arithmeticPolygonComparisonChart hπ data H m j hj u hu
local notation "Y" => arithmeticFactorRatioPolygon π m W (π ^ 1)
  H.a1_unit H.scale_div (j + 1)
local notation "C" => fun (a b : ArithmeticChartLabel (j + 1)) ↦
  pullback.fst (c a) (c b) ≫ F a = pullback.snd (c a) (c b) ≫ F b

/-- The constructed polygon charts agree on all full intersections in the exterior. -/
theorem arithmeticPolygonExterior_compatible (a b : ArithmeticExteriorLabel (j + 1)) :
    C a.val b.val := by
  have hd (i) : C i i :=
    congrArg (fun t ↦ t ≫ F i) ((cancel_mono (c i)).mp pullback.condition)
  have hf (i k) : C i k → C k i :=
    TernaryOpenDescent.flip_compatible (c i) (c k) (F i) (F k)
  have hInf := arithmeticPolygonComparisonChart_infinity hπ data H m j hj u hu
  have hi := (arithmeticInitialInfinity_compatible_iff hπ data H m (j + 1) hj F).mp hInf
  have hii := arithmeticInitialInfinity_initial_compatible hπ data H m (j + 1) hj F hInf
  have hbi (b : Bool) : C .infinity (.initial b) := by
    cases b
    · exact hi.1
    · exact hi.2
  have hbb (b d : Bool) : C (.initial b) (.initial d) := by
    cases b <;> cases d
    · exact hd _
    · exact hii
    · exact hf _ _ hii
    · exact hd _
  have hri (a : Fin (j + 1)) (b : Bool) : C (.retained a b) .infinity :=
    TernaryOpenDescent.disjoint_compatible _ _ _ _
      (arithmeticLabeledAtlas_retained_infinity_disjoint_of_coefficients
        hπ data H m (j + 1) hj a b)
  have hir (a : Fin (j + 1)) (b d : Bool) : C (.initial b) (.retained a d) :=
    arithmeticPositive_initial_retained_compatible hπ data H m j hj F
      (arithmeticPolygonComparisonChart_initial hπ data H m j hj u hu) a b d
  obtain ⟨a, ha⟩ := a
  obtain ⟨b, hb⟩ := b
  cases a with
  | terminal => exact (ha rfl).elim
  | infinity =>
    cases b with
    | terminal => exact (hb rfl).elim
    | infinity => exact hd _
    | initial d => exact hbi d
    | retained idx d => exact hf _ _ (hri idx d)
  | initial d =>
    cases b with
    | terminal => exact (hb rfl).elim
    | infinity => exact hf _ _ (hbi d)
    | initial e => exact hbb d e
    | retained idx e => exact hir idx d e
  | retained idx d =>
    cases b with
    | terminal => exact (hb rfl).elim
    | infinity => exact hri idx d
    | initial e => exact hf _ _ (hir idx e d)
    | retained idx' e =>
      exact arithmeticPositive_retained_compatible hπ data H m j hj F
        (arithmeticPolygonComparisonChart_adjacent hπ data H m j hj u hu) idx idx' d e

/-- The exterior is the actual global-model union of all original nonterminal charts. -/
def arithmeticPolygonExterior :
    (finiteGlobalArithmeticStage hπ data (j + 1) hj m).Opens :=
  openImageUnion (fun i : ArithmeticExteriorLabel (j + 1) ↦ c i.val)

/-- The constructed comparison is defined on the whole exterior, with all overlaps retained. -/
def arithmeticPolygonExteriorMap :
    (arithmeticPolygonExterior hπ data H m j hj).toScheme ⟶ Y :=
  openImageUnionGlue (fun i : ArithmeticExteriorLabel (j + 1) ↦ c i.val)
    (fun i ↦ F i.val) (arithmeticPolygonExterior_compatible hπ data H m j hj u hu)

/-- The exterior comparison recovers every original corrected labeled map exactly. -/
@[reassoc] theorem arithmeticPolygonExteriorMap_chart
    (i : ArithmeticExteriorLabel (j + 1)) :
    openImageUnionMap (fun a : ArithmeticExteriorLabel (j + 1) ↦ c a.val) i ≫
      arithmeticPolygonExteriorMap hπ data H m j hj u hu = F i.val :=
  openImageUnionGlue_fac _ _ _ i

/-- The whole exterior comparison is uniquely determined by the original labeled maps. -/
theorem arithmeticPolygonExteriorMap_unique
    (g : (arithmeticPolygonExterior hπ data H m j hj).toScheme ⟶ Y)
    (hg : ∀ i : ArithmeticExteriorLabel (j + 1),
      openImageUnionMap (fun a : ArithmeticExteriorLabel (j + 1) ↦ c a.val) i ≫ g = F i.val) :
    g = arithmeticPolygonExteriorMap hπ data H m j hj u hu := by
  apply openImageUnion_hom_ext (fun i : ArithmeticExteriorLabel (j + 1) ↦ c i.val)
  intro i
  rw [hg, arithmeticPolygonExteriorMap_chart]

end FLT.Mazur.WeierstrassDividedDepth
