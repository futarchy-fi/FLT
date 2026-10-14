/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeRelationSeedComparisonSquare
public import FLT.Mazur.SchemeRelationSeedGenericImage

/-!
# An exact generic criterion using nonsplit seed certificates

For a nonempty seed etale over the original coefficient target, full generic
kernel image coverage is equivalent to generic seed image certificates and
original source orbit coverage. Neither condition can be silently dropped;
no global full seed kernel or monic coefficient map is assumed.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
universe u
namespace FLT.Mazur.SchemeRelationSeedKernelTransport
set_option backward.isDefEq.respectTransparency false
variable {S T Z : Scheme.{u}} {D A : Over S} {p q : D ⟶ A}
  (e : CategoryTheory.EquivalenceRelation p q) (w : A.left ⟶ T)
  (h : p.left ≫ w = q.left ≫ w) (a : Z ⟶ A.left)
local notation "C" => (pullback (a ≫ w) (a ≫ w) : Scheme)
local notation "K" => (pullback w w : Scheme)
local notation "m" => pullback.lift p.left q.left h
local notation "s" => seedComparison w h a

include e in
/-- The original fiber image certificate restricts to every seed kernel branch. -/
theorem seed_fiber_image_of_original (t : T)
    (hg : ∀ x : K, (pullback.fst w w ≫ w) x = t → x ∈ Set.range m) :
    ∀ z : C, (pullback.fst (a ≫ w) (a ≫ w) ≫ (a ≫ w)) z = t → z ∈ Set.range s := by
  intro z hz
  apply (mem_seed_image_iff e w h a z).mpr
  apply hg
  have H : seedToOriginalKernel w a ≫ pullback.fst w w ≫ w =
      pullback.fst (a ≫ w) (a ≫ w) ≫ (a ≫ w) := by
    rw [seedToOriginalKernel_fst_assoc]
  exact (congrArg (fun f ↦ f z) H).trans hz

include e in
/-- The exact criterion isolates the two genuinely required generic constructions. -/
theorem generic_image_iff_seed_and_orbits [IrreducibleSpace T]
    [Etale (a ≫ w)] [Nonempty Z] :
    (∀ x : K, (pullback.fst w w ≫ w) x = genericPoint T → x ∈ Set.range m) ↔
    (∀ z : C, (pullback.fst (a ≫ w) (a ≫ w) ≫ (a ≫ w)) z = genericPoint T →
      z ∈ Set.range s) ∧
    (∀ x : A.left, w x = genericPoint T →
      ∃ z : Z, RelativeRelationOrbit.Related p q x (a z)) := by
  constructor
  · intro hg
    refine ⟨seed_fiber_image_of_original e w h a (genericPoint T) hg, ?_⟩
    obtain ⟨z, hz⟩ := SchemeRelationEtaleBranchPropagation.exists_generic_seed w a
    intro x hx
    apply (SchemeRelationMonicSeedKernel.mem_branch_iff_related a x).mp
    apply SchemeRelationEtaleBranchPropagation.fiber_subset_branch p.left q.left w h a z
    · intro y hy
      exact hg y (hy.trans hz)
    · exact hx.trans hz.symm
  · rintro ⟨hs, hc⟩
    exact generic_image e w h a hs hc

end FLT.Mazur.SchemeRelationSeedKernelTransport
