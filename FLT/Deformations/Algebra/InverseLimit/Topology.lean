/-
Copyright (c) 2025 Javier López-Contreras. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Javier López-Contreras, Kevin Buzzard
-/
module

public import FLT.Deformations.ContinuousRepresentation.IsTopologicalModule
public import FLT.Deformations.Algebra.InverseLimit.Basic
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Algebra.LinearTopology
public import Mathlib.Topology.Compactness.Compact
public import Mathlib.Topology.Separation.Hausdorff
public import Mathlib.RingTheory.Ideal.Maps

/-!
# Topology on inverse limits

The inverse limit of a system of topological algebraic structures inherits
a natural topological structure as a subspace of the product. We record
basic continuity properties of the canonical maps.
-/

@[expose] public section

open TopologicalSpace

variable {ι : Type*} [Preorder ι] {G : ι → Type*}
variable {T : ∀ ⦃i j : ι⦄, i ≤ j → Type*} {f : ∀ _ _ h, T h}
variable [∀ i j (h : i ≤ j), FunLike (T h) (G j) (G i)]
variable [∀ i : ι, TopologicalSpace (G i)]
  {cont : ∀ {i j}, (h : i ≤ j) → Continuous (f i j h)}

namespace InverseLimit

variable {W : Type*} {M : ι → Type*} (maps : ∀ i, M i) [∀ i, FunLike (M i) W (G i)]
variable (inverseSystemHom : InverseSystemHom G f maps)
variable [TopologicalSpace W]
variable (maps_cont : (i : ι) → Continuous (maps i))

instance : TopologicalSpace (InverseLimit G f) :=
  inferInstanceAs (TopologicalSpace {x : (i : ι) → G i // ∀ i j h, f i j h (x j) = x i})

@[fun_prop, continuity]
lemma val_continuous : Continuous (fun (x : InverseLimit G f) ↦ x.val) := by
  continuity

section ToComponent

@[fun_prop, continuity]
lemma toComponent_continuous (i : ι) : Continuous (toComponent G f i) := by
  rw [toComponent_def]
  have : (fun (z : InverseLimit G f) ↦ z.val i) = (fun y ↦ y i) ∘ (fun z ↦ z.val) := rfl
  rw [this]
  exact Continuous.comp (by fun_prop) (val_continuous ..)

end ToComponent

section Maps

@[fun_prop, continuity]
lemma lift_continuous (maps_cont : ∀ i, Continuous (maps i)) :
    Continuous (lift G f maps inverseSystemHom) := by
  rw [lift_def]
  fun_prop

end Maps

section TopologicalStructures

instance [∀ i, T2Space (G i)] : T2Space (InverseLimit G f) := by
  exact T2Space.of_injective_continuous Subtype.val_injective (val_continuous (G := G) (f := f))

lemma compactSpace [∀ i, T2Space (G i)] [∀ i, CompactSpace (G i)]
    (hcont : ∀ {i j}, (h : i ≤ j) → Continuous (f i j h)) :
    CompactSpace (InverseLimit G f) := by
  unfold InverseLimit
  apply (IsClosed.isClosedEmbedding_subtypeVal ?_).compactSpace
  change IsClosed ({x : (i : ι) → G i | ∀ i j h, f i j h (x j) = x i} :
    Set ((i : ι) → G i))
  simp only [Set.ofPred_forall]
  exact isClosed_iInter fun i ↦ isClosed_iInter fun j ↦ isClosed_iInter fun h ↦
    isClosed_eq ((hcont h).comp (continuous_apply j))
      (continuous_apply i)

instance [∀ i, Group (G i)] [∀ i j h, MonoidHomClass (T h) (G j) (G i)]
    [∀ i : ι, IsTopologicalGroup (G i)] :
    IsTopologicalGroup (InverseLimit G f) := by
  unfold InverseLimit
  let S : Subgroup ((i : ι) → G i) := {
    carrier := { x | ∀ (i j : ι) (h : i ≤ j), (f i j h) (x j) = x i }
    mul_mem' := by aesop
    one_mem' := by aesop
    inv_mem' := by aesop
  }
  change IsTopologicalGroup S
  infer_instance

instance [∀ i, Ring (G i)] [∀ i j h, RingHomClass (T h) (G j) (G i)]
    [∀ i : ι, IsTopologicalRing (G i)] :
    IsTopologicalRing (InverseLimit G f) := by
  unfold InverseLimit
  let S : Subring ((i : ι) → G i) := {
    carrier := { x | ∀ (i j : ι) (h : i ≤ j), (f i j h) (x j) = x i }
    mul_mem' := by aesop
    one_mem' := by aesop
    add_mem' := by aesop
    zero_mem' := by aesop
    neg_mem' := by aesop
  }
  change IsTopologicalRing S
  infer_instance

private def basisIdeal [∀ i, CommRing (G i)]
    [∀ i j h, RingHomClass (T h) (G j) (G i)]
    (I : Set ι) (J : ∀ i, Ideal (G i)) : Ideal (InverseLimit G f) :=
  ⨅ i, ⨅ (_ : i ∈ I), Ideal.comap (toComponentRingHom G f i) (J i)

omit [∀ i, TopologicalSpace (G i)] in
private lemma coe_basisIdeal [∀ i, CommRing (G i)]
    [∀ i j h, RingHomClass (T h) (G j) (G i)]
    (I : Set ι) (J : ∀ i, Ideal (G i)) :
    (basisIdeal (G := G) (f := f) I J : Set (InverseLimit G f)) =
      (fun x ↦ x.val) ⁻¹' (I.pi fun i ↦ (J i : Set (G i))) := by
  ext x
  simp [basisIdeal, Set.pi, toComponentRingHom]
  rfl

instance [∀ i, CommRing (G i)]
    [∀ i j h, RingHomClass (T h) (G j) (G i)]
    [∀ i, IsTopologicalRing (G i)] [∀ i, IsLinearTopology (G i) (G i)] :
    IsLinearTopology (InverseLimit G f) (InverseLimit G f) := by
  have hb : (nhds (0 : InverseLimit G f)).HasBasis
      (fun IJ : Set ι × ∀ i, Ideal (G i) ↦
        IJ.1.Finite ∧ ∀ i ∈ IJ.1, IsOpen (IJ.2 i : Set (G i)))
      (fun IJ ↦ (basisIdeal (G := G) (f := f) IJ.1 IJ.2 :
        Set (InverseLimit G f))) := by
    have hnhds : nhds (0 : InverseLimit G f) =
        Filter.comap (fun x : InverseLimit G f ↦ x.val) (nhds (0 : ∀ i, G i)) := by
      change @nhds (InverseLimit G f)
        (TopologicalSpace.induced (fun x : InverseLimit G f ↦ x.val) inferInstance) 0 = _
      exact nhds_induced _ _
    rw [hnhds, nhds_pi]
    let h := (Filter.hasBasis_pi fun i ↦
      IsLinearTopology.hasBasis_open_ideal (R := G i)).comap
        (fun x : InverseLimit G f ↦ x.val)
    exact h.congr (fun _ ↦ Iff.rfl) fun IJ _ ↦ (coe_basisIdeal IJ.1 IJ.2).symm
  exact IsLinearTopology.mk_of_hasBasis (InverseLimit G f) hb

instance {R : Type*} [Ring R] [TopologicalSpace R]
    [∀ i, AddCommGroup (G i)] [∀ i, Module R (G i)]
    [∀ i j h, LinearMapClass (T h) R (G j) (G i)]
    [∀ i : ι, IsTopologicalModule R (G i)] : IsTopologicalModule R (InverseLimit G f) := by
  unfold InverseLimit
  let S : Submodule R ((i : ι) → G i) := {
    carrier := { x | ∀ (i j : ι) (h : i ≤ j), (f i j h) (x j) = x i }
    add_mem' := by aesop
    zero_mem' := by aesop
    smul_mem' := by aesop
  }
  change IsTopologicalModule R S
  infer_instance


end TopologicalStructures

end InverseLimit
