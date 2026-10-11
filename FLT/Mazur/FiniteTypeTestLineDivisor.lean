/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteTypeTestSectionCartier

/-!
# Canonical full divisors of arbitrary acyclic test lines

The actual rank-one direct image constructs the normalized section by inverse
biduality. Its original full zero ideal is a relative Cartier divisor on every
test scheme, for every independently specified geometric acyclic rank-one line.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
namespace FLT.Mazur.CartierAbel
open FCurve
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] ModuleSheafTensor.tensor twistedSectionPushforwardEquiv
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R]
  {X Y S : Scheme.{0}} {a : X ⟶ Y} {f : X ⟶ S}
  {q : Y ⟶ Spec (.of R)} {g : S ⟶ Spec (.of R)}
  [IsProper q] [Flat q] [GeometricallyIntegral q] (h : IsPullback a f q g)
  (L : X.Modules) (hL : LocallyFreeRankOne L) (hA : GeometricAcyclicRankOne f L)

/-- Recover a relative section from an original split map, preserving its twist and section. -/
@[irreducible] def SplitDirectImageSection.toFiniteTypeTestRelative
    (b : SplitDirectImageSection f L) : RelativeSection f L hL := by
  let s := (twistedSectionPushforwardEquiv f L b.baseLine.property).symm b.map
  have hs : SplitLineAffineNeighborhood.LocallySplit
      (twistedSectionPushforwardEquiv f L b.baseLine.property s) := by
    simpa only [s, Equiv.apply_symm_apply] using b.locallySplit
  have hc := finiteTypeTest_section_relativeCartier h L hL hA b.baseLine.property s hs
  exact ⟨⟨b.baseLine, s, hc.1⟩, hc.2.2⟩

/-- The canonical normalized section for an arbitrary line on an unrestricted test. -/
@[irreducible] def finiteTypeTestLineSection : RelativeSection f L hL := by
  let b := rankOneSplitSection f L
    ((finiteTypeTest_geometricAcyclicRankOne_iff_actual h L hL).mp hA).2
  exact b.toFiniteTypeTestRelative h L hL hA

/-- The full Cartier divisor defined by the original normalized section. -/
@[irreducible] def finiteTypeTestLineDivisor : RelativeFiber f L hL :=
  relativeSectionToFiber f L hL (finiteTypeTestLineSection h L hL hA)

/-- The construction retains the full zero ideal of the actual original normalized section. -/
lemma finiteTypeTestLineDivisor_ideal :
    (finiteTypeTestLineDivisor h L hL hA).val.val.val =
      lineSectionZeroIdeal (twist_rankOne f L hL (finiteTypeTestLineSection h L hL hA).val.baseLine)
        (finiteTypeTestLineSection h L hL hA).val.section_ := by
  unfold finiteTypeTestLineDivisor
  rfl

/-- Every full relative Cartier divisor with the prescribed class is the constructed divisor. -/
theorem finiteTypeTestLineDivisor_unique (D : RelativeFiber f L hL) :
    D = finiteTypeTestLineDivisor h L hL hA := by
  let _ : Surjective f := MorphismProperty.of_isPullback h inferInstance
  let _ := rankOne_relativeFiber_subsingleton f L hL
    ((finiteTypeTest_geometricAcyclicRankOne_iff_actual h L hL).mp hA).2
  exact Subsingleton.elim _ _

/-- The full relative Abel fiber is inhabited and unique for every independent acyclic test line. -/
@[instance_reducible] def finiteTypeTestLineFiberUnique : Unique (RelativeFiber f L hL) where
  default := finiteTypeTestLineDivisor h L hL hA
  uniq := finiteTypeTestLineDivisor_unique h L hL hA

end FLT.Mazur.CartierAbel
