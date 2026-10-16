/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedTwistedExteriorComparison
public import FLT.Mazur.WeierstrassDividedArithmeticLabeledSystem
public import FLT.Mazur.WeierstrassDividedClosingTransportRestriction

/-!
# Actual coefficient restrictions on the complete normalized atlas

The normalized retained and terminal charts use the same explicit smoothing
coefficient map. The true retained branch keeps its coordinate swap. These
full squares identify the restriction on the simultaneous glued target.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX WeierstrassDilatation
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] finiteGlobalModel finiteGlobalContraction
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (m j : ℕ) (hj : j + 1 ≤ n)
local notation "A" => fun k ↦ twistedArithmeticAtlasObject hπ data H k j hj
local notation "r" => arithmeticLabeledAtlasRestriction hπ data H m (j + 1) hj
local notation "N" => closingNormalizedRestriction data H m

/-- The actual coefficient maps on all normalized charts, including the full terminal node. -/
def twistedArithmeticAtlasRestriction (i : ArithmeticChartLabel (j + 1)) :
    A m i ⟶ A (m + 1) i :=
  match i with
  | .terminal => N
  | .retained _ _ => N
  | .infinity => r .infinity
  | .initial b => r (.initial b)

variable (u : Rˣ) (hu : (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "e" => fun k ↦ twistedArithmeticAtlasIso hπ data H k j hj u hu
local notation "ρ" => twistedArithmeticAtlasRestriction hπ data H m j hj
local notation "d" => data (Fin.mk (j + 1) (Nat.lt_succ_of_le hj))

omit [IsBezout R] in
/-- Each whole-chart comparison preserves the explicit normalized coefficient map. -/
@[reassoc] theorem twistedArithmeticAtlasIso_restriction
    (i : ArithmeticChartLabel (j + 1)) :
    r i ≫ (e (m + 1) i).hom = (e m i).hom ≫ ρ i := by
  cases i with
  | infinity => exact (Category.comp_id _).trans (Category.id_comp _).symm
  | initial b => exact (Category.comp_id _).trans (Category.id_comp _).symm
  | terminal =>
    exact fixedTerminalPolygonIso_restriction π W (π ^ (1 + j + 1))
      (Data.b3 d) (Data.b4 d) (Data.b6 d) H.a1_unit (H.scale (j + 1)) H.a2_div
      (H.b3_div _) (H.b4_div _) (H.b6_div _) u hu hπ m
  | retained idx b =>
    have hc : closingRetainedRestriction (R := R) (π := π) m ≫
        (arithmeticRetainedFixedSmoothingIso data H (m + 1) (j + 1) hj idx).hom =
        (arithmeticRetainedFixedSmoothingIso data H m (j + 1) hj idx).hom ≫ N :=
      arithmeticRetainedFixedSmoothingIso_restriction data H m (j + 1) hj idx
    change WeierstrassSuccessiveX.arithmeticPolygonNodeRestriction R π m ≫
      (arithmeticRetainedFixedSmoothingIso data H (m + 1) (j + 1) hj idx).hom ≫
      (twistedRetainedOrientation data H (m + 1) b).hom =
      ((arithmeticRetainedFixedSmoothingIso data H m (j + 1) hj idx).hom ≫
        (twistedRetainedOrientation data H m b).hom) ≫ N
    rw [arithmeticRetainedPolygonRestriction_eq]
    change closingRetainedRestriction (R := R) (π := π) m ≫ _ ≫ _ = _
    rw [← Category.assoc, hc, Category.assoc,
      Category.assoc]
    congr 1
    cases b
    · exact (Category.comp_id _).trans (Category.id_comp _).symm
    · exact (branchSwapIso_ringMap (restriction R π m).toRingHom _ _
        (arithmeticInitialMobiusSmoothing_restriction W H.a1_unit (π ^ 1) π m)).symm

omit [IsBezout R] in
/-- The constructed inverse also preserves each complete normalized coefficient square. -/
@[reassoc] theorem twistedArithmeticAtlasIso_inv_restriction
    (i : ArithmeticChartLabel (j + 1)) :
    ρ i ≫ (e (m + 1) i).inv = (e m i).inv ≫ r i := by
  apply (cancel_epi (e m i).hom).mp
  rw [← Category.assoc, ← twistedArithmeticAtlasIso_restriction,
    Category.assoc, Iso.hom_inv_id, Category.comp_id, Iso.hom_inv_id_assoc]

local notation "G" => fun k ↦ simultaneousTwistedArithmeticIso hπ data H k j hj u hu
local notation "ι" => fun k ↦ simultaneousTwistedArithmeticChart hπ data H k j hj u hu
local notation "c" => fun k ↦ arithmeticLabeledAtlasMap hπ data H k (j + 1) hj
local notation "q" => finiteGlobalArithmeticRestriction hπ data (j + 1) hj m

/-- The complete twisted target inherits its actual global arithmetic quotient arrow. -/
def simultaneousTwistedArithmeticRestriction :
    simultaneousTwistedArithmeticStage hπ data H m j hj u hu ⟶
      simultaneousTwistedArithmeticStage hπ data H (m + 1) j hj u hu :=
  (G m).inv ≫ q ≫ (G (m + 1)).hom

/-- The original-to-twisted global isomorphism preserves the entire quotient arrow. -/
@[reassoc] theorem simultaneousTwistedArithmeticIso_restriction :
    (G m).hom ≫ simultaneousTwistedArithmeticRestriction hπ data H m j hj u hu =
      q ≫ (G (m + 1)).hom := by
  rw [simultaneousTwistedArithmeticRestriction, Iso.hom_inv_id_assoc]

/-- Every full normalized chart has exactly its explicit coefficient restriction in the target. -/
@[reassoc] theorem simultaneousTwistedArithmeticChart_restriction
    (i : ArithmeticChartLabel (j + 1)) :
    ρ i ≫ ι (m + 1) i =
      ι m i ≫ simultaneousTwistedArithmeticRestriction hπ data H m j hj u hu := by
  apply (cancel_epi (e m i).hom).mp
  rw [← Category.assoc, ← twistedArithmeticAtlasIso_restriction, Category.assoc,
    ← simultaneousTwistedArithmeticIso_chart,
    ← Category.assoc, arithmeticLabeledAtlasMap_restriction, Category.assoc,
    ← simultaneousTwistedArithmeticIso_restriction,
    ← Category.assoc, simultaneousTwistedArithmeticIso_chart, Category.assoc]

local notation "Q" => Quotient R π m
local notation "τ" => arithmeticInitialMobiusSmoothing W H.a1_unit (π ^ 1) π m
local notation "hn" => Fact.mk
  (arithmeticInitialFactorRatioSmoothing_nilpotent W H.a1_unit (π ^ 1) π m H.scale_div)

omit [IsBezout R] in
/-- The original retained comparison factors through its exact normalized polygon label. -/
theorem twistedArithmeticRetained_polygon (idx : Fin (j + 1)) (b : Bool) :
    let _ := hn
    (e m (.retained idx b)).hom ≫ PolygonInfinitesimal.chart Q τ
      (2 * (j + 1) + 3) (by omega) (retainedPolygonIndex (j + 1) idx b) =
        arithmeticPolygonComparisonChart hπ data H m j hj u hu (.retained idx b) := by
  let _ := hn
  cases b <;> exact Category.assoc _ _ _

/-- The twisted exterior uses the prescribed index on each entire normalized retained node. -/
@[reassoc] theorem twistedArithmeticExteriorPolygonMap_retained
    (idx : Fin (j + 1)) (b : Bool) :
    let _ := hn
    openImageUnionMap
      (fun i : ArithmeticExteriorLabel (j + 1) ↦ ι m i.val)
      ⟨.retained idx b, by simp⟩ ≫
        twistedArithmeticExteriorPolygonMap hπ data H m j hj u hu =
      PolygonInfinitesimal.chart Q τ (2 * (j + 1) + 3) (by omega)
        (retainedPolygonIndex (j + 1) idx b) := by
  let _ := hn
  rw [twistedArithmeticExteriorPolygonMap_chart]
  rw [← twistedArithmeticRetained_polygon hπ data H m j hj u hu idx b,
    Iso.inv_hom_id_assoc]

end FLT.Mazur.WeierstrassDividedDepth
