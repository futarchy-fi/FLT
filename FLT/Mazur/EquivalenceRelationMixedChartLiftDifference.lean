/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EquivalenceRelationJointChartLiftDifference
public import FLT.Mazur.EquivalenceRelationMixedChartDescent

/-!
# Exact lift discrepancies on the entire original mixed relation

Faithfully flat detection descends common-frame boundary agreement to the
original mixed chart relation. The discrepancy lies in its exact boundary
kernel; it is not asserted to vanish in the ambient section ring.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationNormalizedFrames.MixedFrames
open InvariantBoundary
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] EquivalenceRelationNormalizedFrames.source
  InvariantBoundary.boundary relation jointBoundaryTarget
  mixedChartFirst mixedChartSecond mixedChartBoundaryInclusion jointChartMap
  jointChartFirst jointChartSecond jointChartOpen mixedChartOpen
  InvariantBoundary.inclusion InvariantBoundary.endpoint
variable {D A B C : Scheme.{0}} {p q : D ⟶ A} [IsSeparated p] [Etale p]
  (e : CategoryTheory.EquivalenceRelation p q)
  {I J : Type} [Fintype I] [Fintype J] (o : I) (o' : J)
  (U : (source p q I o).Opens) (V : (source p q J o').Opens)
  (i : B ⟶ A) (z : C ⟶ D) (r s : C ⟶ B)
  (hr : IsPullback z r p i) (hs : z ≫ q = s ≫ i)
local notation "j₁" => InvariantBoundary.inclusion (p := p) (q := q) I o i
local notation "j₂" => InvariantBoundary.inclusion (p := p) (q := q) J o' i
local notation "b₁" => endpoint (p := p) (q := q) I o i
local notation "b₂" => endpoint (p := p) (q := q) J o' i
local notation "F" => mixedChartFirst o o' U V
local notation "G" => mixedChartSecond o o' U V
local notation "j" => mixedChartBoundaryInclusion o o' U V i

omit [Etale p] in
/-- The full ambient discrepancy pulls back to the common-frame discrepancy. -/
theorem mixedChart_difference_pullback (a : Γ(U.toScheme, ⊤)) (b : Γ(V.toScheme, ⊤))
    (c : JointIndex I J) :
    (jointChartMap e o o' U V c).appTop ((F).appTop a - (G).appTop b) =
      (jointChartFirst e o o' c.2.val.1 c.2.val.2 U V).appTop a -
        (jointChartSecond e o o' c.2.val.1 c.2.val.2 U V).appTop b := by
  have hf := congrArg (fun f ↦ f.appTop a) (jointChartMap_first e o o' U V c)
  have hg := congrArg (fun f ↦ f.appTop b) (jointChartMap_second e o o' U V c)
  simp only [Scheme.Hom.comp_appTop, ConcreteCategory.comp_apply] at hf hg
  exact (map_sub (jointChartMap e o o' U V c).appTop.hom _ _).trans
    (congrArg₂ (fun x y ↦ x - y) hf hg)

include e hr hs

/-- Arbitrary actual lifts differ by an exact boundary section on the full mixed relation. -/
theorem mixedChart_lifts_sub_mem_kernel (E : B.Opens) (hE : r ⁻¹ᵁ E = s ⁻¹ᵁ E)
    (hU : (j₁) ⁻¹ᵁ U ≤ (b₁) ⁻¹ᵁ E) (hV : (j₂) ⁻¹ᵁ V ≤ (b₂) ⁻¹ᵁ E)
    (t : Γ(E.toScheme, ⊤)) (ht : (r ∣_ E).appTop t = (s.resLE E _ hE.le).appTop t)
    (a : Γ(U.toScheme, ⊤)) (b : Γ(V.toScheme, ⊤))
    (ha : ((j₁) ∣_ U).appTop a = ((b₁).resLE E _ hU).appTop t)
    (hb : ((j₂) ∣_ V).appTop b = ((b₂).resLE E _ hV).appTop t) :
    (F).appTop a - (G).appTop b ∈ RingHom.ker (j).appTop.hom := by
  apply (mixedChart_mem_boundary_kernel_iff e o o' U V i _).mpr
  intro c
  have h := jointChart_lifts_sub_mem_kernel e o o' c.2.val.1 c.2.val.2 U V
    i z r s hr hs E hE hU hV t ht a b ha hb
  simpa only [mixedChart_difference_pullback] using h

/-- Full boundary equality survives any scheme test, including nonreduced tests. -/
theorem mixedChart_lifts_boundary_test {T : Scheme.{0}}
    (g : T ⟶ (mixedChartBoundaryOpen o o' U V i).toScheme)
    (E : B.Opens) (hE : r ⁻¹ᵁ E = s ⁻¹ᵁ E)
    (hU : (j₁) ⁻¹ᵁ U ≤ (b₁) ⁻¹ᵁ E) (hV : (j₂) ⁻¹ᵁ V ≤ (b₂) ⁻¹ᵁ E)
    (t : Γ(E.toScheme, ⊤)) (ht : (r ∣_ E).appTop t = (s.resLE E _ hE.le).appTop t)
    (a : Γ(U.toScheme, ⊤)) (b : Γ(V.toScheme, ⊤))
    (ha : ((j₁) ∣_ U).appTop a = ((b₁).resLE E _ hU).appTop t)
    (hb : ((j₂) ∣_ V).appTop b = ((b₂).resLE E _ hV).appTop t) :
    (g ≫ j ≫ F).appTop a = (g ≫ j ≫ G).appTop b := by
  have h := mixedChart_lifts_sub_mem_kernel e o o' U V i z r s hr hs
    E hE hU hV t ht a b ha hb
  change (j).appTop ((F).appTop a - (G).appTop b) = 0 at h
  rw [map_sub, sub_eq_zero] at h
  simpa only [Scheme.Hom.comp_appTop, ConcreteCategory.comp_apply] using
    congrArg (fun x ↦ g.appTop x) h

end FLT.Mazur.EquivalenceRelationNormalizedFrames.MixedFrames
