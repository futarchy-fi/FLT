/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeRelationSeedKernelTransport
public import FLT.Mazur.SchemeRelationSeedOrbit

/-!
# Whole kernel fibers from partial nonsplit seed certificates

Only the seed kernel fiber over the selected coefficient point needs image
certificates. Original source orbit coverage transports these certificates to
all points of the original coefficient kernel, with their residue-field
branches retained. No full seed kernel or monic seed hypothesis is used.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
universe u
namespace FLT.Mazur.SchemeRelationSeedKernelTransport
set_option backward.isDefEq.respectTransparency false
variable {S T Z : Scheme.{u}} {D A : Over S} {p q : D ⟶ A}
  (e : CategoryTheory.EquivalenceRelation p q) (w : A.left ⟶ T)
  (h : p.left ≫ w = q.left ≫ w) (a : Z ⟶ A.left)
local notation "b" => SchemeRelationEtaleBranchPropagation.branch p.left q.left a
local notation "m" => pullback.lift p.left q.left h
local notation "K" => (pullback w w : Scheme)
local notation "C" => (pullback (a ≫ w) (a ≫ w) : Scheme)

/-- Transport leaves the coefficient morphism unchanged, including its structure-sheaf map. -/
theorem toSeedKernel_coefficient : toSeedKernel w h a ≫
    pullback.fst (a ≫ w) (a ≫ w) ≫ (a ≫ w) =
      toOriginalKernel (p := p) (q := q) w a ≫ pullback.fst w w ≫ w := by
  rw [toSeedKernel_fst_assoc, toOriginalKernel_fst_assoc]
  rw [SchemeRelationEtaleBranchPropagation.branch_comp p.left q.left w h a]

include e in
/-- Partial seed certificates cover an entire original kernel fiber after orbit propagation. -/
theorem fiber_subset_image (t : T)
    (hs : ∀ z : C, (pullback.fst (a ≫ w) (a ≫ w) ≫ (a ≫ w)) z = t →
      z ∈ Set.range (seedComparison w h a))
    (hc : ∀ x : A.left, w x = t → x ∈ Set.range b) :
    ∀ x : K, (pullback.fst w w ≫ w) x = t → x ∈ Set.range m := by
  intro x hx
  have hy : w (pullback.snd w w x) = t :=
    (congrArg (fun g ↦ g x) (pullback.condition (f := w) (g := w))).symm.trans hx
  have hr : x ∈ Set.range (toOriginalKernel (p := p) (q := q) w a) := by
    rw [toOriginalKernel, Scheme.Pullback.range_map]
    exact ⟨hc _ hx, hc _ hy⟩
  obtain ⟨z, hz⟩ := hr
  rw [← hz]
  apply mem_image e w h a z
  apply hs
  have H := congrArg (fun f ↦ f z) (toSeedKernel_coefficient w h a)
  change (pullback.fst (a ≫ w) (a ≫ w) ≫ (a ≫ w)) (toSeedKernel w h a z) =
    (pullback.fst w w ≫ w) (toOriginalKernel (p := p) (q := q) w a z) at H
  exact H.trans ((congrArg (pullback.fst w w ≫ w) hz).trans hx)

include e in
/-- Original relation orbits suffice for coverage; no representatives are selected globally. -/
theorem fiber_image_of_orbits (t : T)
    (hs : ∀ z : C, (pullback.fst (a ≫ w) (a ≫ w) ≫ (a ≫ w)) z = t →
      z ∈ Set.range (seedComparison w h a))
    (hc : ∀ x : A.left, w x = t →
      ∃ z : Z, RelativeRelationOrbit.Related p q x (a z)) :
    ∀ x : K, (pullback.fst w w ≫ w) x = t → x ∈ Set.range m :=
  fiber_subset_image e w h a t hs
    (fun x hx ↦ (SchemeRelationMonicSeedKernel.mem_branch_iff_related a x).mpr (hc x hx))

include e in
/-- Only the generic SEED kernel needs certificates to cover the generic ORIGINAL kernel. -/
theorem generic_image [IrreducibleSpace T]
    (hs : ∀ z : C, (pullback.fst (a ≫ w) (a ≫ w) ≫ (a ≫ w)) z = genericPoint T →
      z ∈ Set.range (seedComparison w h a))
    (hc : ∀ x : A.left, w x = genericPoint T →
      ∃ z : Z, RelativeRelationOrbit.Related p q x (a z)) :
    ∀ x : K, (pullback.fst w w ≫ w) x = genericPoint T → x ∈ Set.range m :=
  fiber_image_of_orbits e w h a (genericPoint T) hs hc

end FLT.Mazur.SchemeRelationSeedKernelTransport
