/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeRelationOpenSelectorFibers

/-!
# Two original coordinates on a common selector chart

Pull back the source cover along the first coordinate. Invariance lifts the
second coordinate into the same chart without identifying either coordinate.
All lifts are scheme morphisms, including their structure-sheaf maps.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace FLT.Mazur.SchemeRelationOpenSelector
open RelativeRelationOrbit
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {S : Scheme.{u}} {D A : Over S} {p q : D ⟶ A}
local notation "B" => Scheme.Opens.toScheme (sourceOpen (p := p) (q := q))
local notation "k" => Scheme.Opens.ι (sourceOpen (p := p) (q := q))

/-- The actual original source chart inclusion into the source union. -/
def sourceChart (U : Chart p q) : U.val.val.toScheme ⟶ B :=
  openImageUnionMap (fun V : Chart p q ↦ V.val.val.ι) U

@[reassoc]
theorem sourceChart_original (U : Chart p q) : sourceChart U ≫ k = U.val.val.ι :=
  openImageUnionMap_fac _ _

/-- Lift a scheme morphism into a literal original open chart. -/
def intoChart (U : Chart p q) {Y : Scheme.{u}} (f : Y ⟶ B)
    (hf : ∀ z, (f z).val ∈ U.val.val) : Y ⟶ U.val.val.toScheme :=
  IsOpenImmersion.lift U.val.val.ι (f ≫ k) (by
    rintro _ ⟨z, rfl⟩
    exact ⟨⟨(f z).val, hf z⟩, rfl⟩)

@[reassoc]
theorem intoChart_original (U : Chart p q) {Y : Scheme.{u}} (f : Y ⟶ B)
    (hf : ∀ z, (f z).val ∈ U.val.val) : intoChart U f hf ≫ U.val.val.ι = f ≫ k :=
  IsOpenImmersion.lift_fac _ _ _

@[reassoc]
theorem intoChart_source (U : Chart p q) {Y : Scheme.{u}} (f : Y ⟶ B)
    (hf : ∀ z, (f z).val ∈ U.val.val) : intoChart U f hf ≫ sourceChart U = f := by
  apply (cancel_mono k).mp
  rw [Category.assoc, sourceChart_original, intoChart_original]

instance sourceChart_isOpenImmersion (U : Chart p q) : IsOpenImmersion (sourceChart U) := by
  unfold sourceChart
  infer_instance

/-- Every point is covered by an original chart, in the fixed source coordinates. -/
theorem sourceChart_exists (z : B) : ∃ (U : Chart p q) (w : U.val.val.toScheme),
    sourceChart U w = z := exists_source_chart z

/-- The chart quotient map is the restriction of the assembled projection. -/
@[reassoc]
theorem sourceChart_projection (e : CategoryTheory.EquivalenceRelation p q) [Etale q.left]
    (U : Chart p q) : sourceChart U ≫ projection e = sourceMap e U := chart_projection e U

attribute [local irreducible] sourceOpen sourceChart
variable {Y : Scheme.{u}}

/-- Cover a test scheme using its first original source coordinate. -/
def testCover (x : Y ⟶ B) : Y.OpenCover.{u} where
  I₀ := Chart p q
  X U := pullback x (sourceChart (p := p) (q := q) U)
  f U := pullback.fst x (sourceChart (p := p) (q := q) U)
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    refine ⟨?_, inferInstance⟩
    intro z
    obtain ⟨U, w, hw⟩ := sourceChart_exists (p := p) (q := q) (x z)
    obtain ⟨t, ht, _⟩ := Scheme.exists_preimage_of_isPullback
      (IsPullback.of_hasPullback x (sourceChart (p := p) (q := q) U)) z w hw.symm
    exact ⟨U, t, ht⟩

local notation "j" => sourceChart (p := p) (q := q)

/-- The first coordinate on a member of the pulled back source cover. -/
def firstChart (x : Y ⟶ B) (U : Chart p q) : pullback x (j U) ⟶ U.val.val.toScheme :=
  pullback.snd x (j U)

@[reassoc]
theorem firstChart_source (x : Y ⟶ B) (U : Chart p q) :
    firstChart x U ≫ j U = pullback.fst x (j U) ≫ x :=
  (pullback.condition (f := x) (g := j U)).symm

@[reassoc]
theorem firstChart_original (x : Y ⟶ B) (U : Chart p q) :
    firstChart x U ≫ U.val.val.ι = pullback.fst x (j U) ≫ x ≫ k := by
  rw [← Category.assoc, ← firstChart_source x U, Category.assoc, sourceChart_original]

/-- Original invariance puts the independent second coordinate in the same open. -/
theorem secondChart_mem (x y : Y ⟶ B) (hr : ∀ z, Related p q (x z).val (y z).val)
    (U : Chart p q) (z : (pullback x (j U) : Scheme.{u})) :
    ((pullback.fst x (j U) ≫ y) z).val ∈ U.val.val := by
  have hx := congrArg (fun a ↦ a z) (firstChart_original x U)
  change (firstChart x U z).val = (x (pullback.fst x (j U) z)).val at hx
  exact (invariant_mem_iff U.val (hr (pullback.fst x (j U) z))).mp
    (hx ▸ (firstChart x U z).property)

/-- The second coordinate is lifted as an entire scheme morphism. -/
def secondChart (x y : Y ⟶ B) (hr : ∀ z, Related p q (x z).val (y z).val)
    (U : Chart p q) : pullback x (j U) ⟶ U.val.val.toScheme :=
  intoChart U (pullback.fst x (j U) ≫ y) (secondChart_mem x y hr U)

@[reassoc]
theorem secondChart_source (x y : Y ⟶ B) (hr : ∀ z, Related p q (x z).val (y z).val)
    (U : Chart p q) : secondChart x y hr U ≫ j U = pullback.fst x (j U) ≫ y :=
  intoChart_source _ _ _

@[reassoc]
theorem secondChart_original (x y : Y ⟶ B) (hr : ∀ z, Related p q (x z).val (y z).val)
    (U : Chart p q) :
    secondChart x y hr U ≫ U.val.val.ι = pullback.fst x (j U) ≫ y ≫ k := by
  rw [secondChart, intoChart_original, Category.assoc]

end FLT.Mazur.SchemeRelationOpenSelector
