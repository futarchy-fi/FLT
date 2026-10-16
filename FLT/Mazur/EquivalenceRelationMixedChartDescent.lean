/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EquivalenceRelationMixedChartProjections
public import FLT.Mazur.SchemeFppfCoverInvariantFunctions

/-!
# Detecting original mixed chart equations on common frames

The exhaustive common-frame covers detect both ambient section equality and
membership in the exact boundary kernel on the original mixed chart relation.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationNormalizedFrames.MixedFrames
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] EquivalenceRelationNormalizedFrames.source
  InvariantBoundary.boundary relation jointBoundaryTarget
variable {D A B : Scheme.{0}} {p q : D ⟶ A} [IsSeparated p] [Etale p]
  (e : CategoryTheory.EquivalenceRelation p q)
  {I J : Type} [Fintype I] [Fintype J] (o : I) (o' : J)
  (U : (source p q I o).Opens) (V : (source p q J o').Opens)
local notation "M" => mixedChartOpen o o' U V

/-- The exhaustive common-chart family is also an actual fppf cover. -/
def jointChartFppfCover : (M).toScheme.Cover Scheme.fppfPrecoverage :=
  Scheme.Cover.mkOfCovers (P := @Flat ⊓ @LocallyOfFinitePresentation) _
    (fun c : JointIndex I J ↦
      (jointChartOpen e o o' c.2.val.1 c.2.val.2 U V).toScheme)
    (jointChartMap e o o' U V) (jointChartMap_covers e o o' U V)
    (fun _ ↦ ⟨inferInstance, inferInstance⟩)

/-- Equality on all common charts is equality on the entire original mixed relation. -/
theorem mixedChart_sections_ext {a b : Γ((M).toScheme, ⊤)}
    (h : ∀ c, (jointChartMap e o o' U V c).appTop a =
      (jointChartMap e o o' U V c).appTop b) : a = b :=
  SchemeFppfFamily.cover_sections_ext (jointChartFppfCover e o o' U V) h

/-- Exact compatibility is detected by all common frames simultaneously. -/
theorem mixedChart_compatible_iff (a : Γ(U.toScheme, ⊤)) (b : Γ(V.toScheme, ⊤)) :
    (mixedChartFirst o o' U V).appTop a = (mixedChartSecond o o' U V).appTop b ↔
      ∀ c : JointIndex I J,
        (jointChartFirst e o o' c.2.val.1 c.2.val.2 U V).appTop a =
          (jointChartSecond e o o' c.2.val.1 c.2.val.2 U V).appTop b := by
  have hf (c : JointIndex I J) :
      (jointChartMap e o o' U V c).appTop ((mixedChartFirst o o' U V).appTop a) =
        (jointChartFirst e o o' c.2.val.1 c.2.val.2 U V).appTop a := by
    simpa only [Scheme.Hom.comp_appTop, ConcreteCategory.comp_apply] using
      congrArg (fun f ↦ f.appTop a) (jointChartMap_first e o o' U V c)
  have hg (c : JointIndex I J) :
      (jointChartMap e o o' U V c).appTop ((mixedChartSecond o o' U V).appTop b) =
        (jointChartSecond e o o' c.2.val.1 c.2.val.2 U V).appTop b := by
    simpa only [Scheme.Hom.comp_appTop, ConcreteCategory.comp_apply] using
      congrArg (fun f ↦ f.appTop b) (jointChartMap_second e o o' U V c)
  constructor
  · intro h c
    rw [← hf, ← hg, h]
  · intro h
    apply mixedChart_sections_ext e o o' U V
    intro c
    rw [hf, hg]
    exact h c

variable (i : B ⟶ A)
local notation "j" => mixedChartBoundaryInclusion o o' U V i

/-- The exhaustive family on the full boundary is an fppf cover. -/
def jointChartBoundaryFppfCover :
    (mixedChartBoundaryOpen o o' U V i).toScheme.Cover Scheme.fppfPrecoverage :=
  Scheme.Cover.mkOfCovers (P := @Flat ⊓ @LocallyOfFinitePresentation) _
    (fun c : JointIndex I J ↦
      (InvariantBoundary.inclusion (Fin c.1.val) (c.2.val.1 o) i ⁻¹ᵁ
        jointChartOpen e o o' c.2.val.1 c.2.val.2 U V).toScheme)
    (jointChartBoundaryMap e o o' U V i) (jointChartBoundaryMap_covers e o o' U V i)
    (fun _ ↦ ⟨inferInstance, inferInstance⟩)

/-- The full original boundary kernel is detected on the entire common-chart boundaries. -/
theorem mixedChart_mem_boundary_kernel_iff (a : Γ((M).toScheme, ⊤)) :
    a ∈ RingHom.ker (j).appTop.hom ↔ ∀ c : JointIndex I J,
      (jointChartMap e o o' U V c).appTop a ∈ RingHom.ker
        (InvariantBoundary.inclusion (Fin c.1.val) (c.2.val.1 o) i ∣_
          jointChartOpen e o o' c.2.val.1 c.2.val.2 U V).appTop.hom := by
  have hcomp (c : JointIndex I J) :
      (jointChartBoundaryMap e o o' U V i c).appTop ((j).appTop a) =
        (InvariantBoundary.inclusion (Fin c.1.val) (c.2.val.1 o) i ∣_
          jointChartOpen e o o' c.2.val.1 c.2.val.2 U V).appTop
            ((jointChartMap e o o' U V c).appTop a) := by
    simpa only [Scheme.Hom.comp_appTop, ConcreteCategory.comp_apply] using
      congrArg (fun f ↦ f.appTop a) (jointChartBoundaryMap_ambient e o o' U V i c)
  change (j).appTop a = 0 ↔ ∀ c, _ = 0
  constructor
  · intro h c
    exact (hcomp c).symm.trans
      ((congrArg (fun x ↦ (jointChartBoundaryMap e o o' U V i c).appTop x) h).trans
        (map_zero _))
  · intro h
    apply SchemeFppfFamily.cover_sections_ext (jointChartBoundaryFppfCover e o o' U V i)
    intro c
    change (jointChartBoundaryMap e o o' U V i c).appTop ((j).appTop a) =
      (jointChartBoundaryMap e o o' U V i c).appTop 0
    exact (hcomp c).trans ((h c).trans (map_zero _).symm)

end FLT.Mazur.EquivalenceRelationNormalizedFrames.MixedFrames
