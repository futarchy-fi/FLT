/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.RaynaudDirectedPolynomial
public import FLT.GroupScheme.RaynaudStageHenselian

/-!
# Henselianity of a directed union of unramified DVR stages

Descend a monic polynomial and its approximate root to one Henselian stage.
The stage inclusion is local because it preserves the common uniformizer,
so Hensel's root lifts back to the union.
-/

@[expose] public noncomputable section

open Polynomial IsLocalRing

namespace RaynaudParameters

variable {R Ω ι : Type*} [CommRing R] [CommRing Ω] [IsDomain Ω]
  [Algebra R Ω] [Nonempty ι] (S : ι → Subalgebra R Ω)
  (hS : Directed (· ≤ ·) S) [∀ i, IsDiscreteValuationRing (S i)]
  [∀ i, HenselianLocalRing (S i)]

include hS

/-- The directed union of Henselian DVR stages with a common uniformizer
is itself Henselian. -/
theorem henselianLocalRing_iSup (π : R)
    (hπ : ∀ i, Irreducible (algebraMap R (S i) π)) :
    HenselianLocalRing (↥(⨆ i, S i)) := by
  let := isDiscreteValuationRing_iSup S hS π hπ
  constructor
  intro f hf x hx hd
  obtain ⟨i, g, y, rfl, rfl⟩ := exists_stage_polynomial S hS f x
  let inc := (Subalgebra.inclusion (le_iSup S i)).toRingHom
  let : IsLocalHom (Subalgebra.inclusion (le_iSup S i)) :=
    isLocalHom_inclusion_iSup S hS π hπ i
  let : IsLocalHom inc := ⟨fun x hx ↦
    isUnit_of_map_unit (Subalgebra.inclusion (le_iSup S i)) x hx⟩
  have hg : g.Monic := Polynomial.monic_of_injective (Subalgebra.inclusion_injective _) hf
  have hgy : g.eval y ∈ maximalIdeal (S i) := by
    intro hu
    change ¬ IsUnit ((g.map inc).eval (inc y)) at hx
    apply hx
    simpa only [Polynomial.eval_map_apply] using hu.map inc
  have hgd : IsUnit (g.derivative.eval y) := by
    apply isUnit_of_map_unit inc (g.derivative.eval y)
    change IsUnit ((g.map inc).derivative.eval (inc y)) at hd
    simpa only [Polynomial.derivative_map, Polynomial.eval_map_apply] using hd
  obtain ⟨z, hz, hzy⟩ := HenselianLocalRing.is_henselian g hg y hgy hgd
  refine ⟨inc z, ?_, ?_⟩
  · change (g.map inc).eval (inc z) = 0
    rw [Polynomial.eval_map_apply, hz, map_zero]
  · change inc z - inc y ∈ maximalIdeal _
    rw [← map_sub]
    exact map_nonunit inc (z - y) hzy

omit [∀ i, HenselianLocalRing (S i)] in
/-- Over a complete DVR, Henselianity of the finite stages is a consequence,
so only finiteness and preservation of the uniformizer are required. -/
theorem henselianLocalRing_iSup_of_complete [IsDomain R] [IsDiscreteValuationRing R]
    [IsAdicComplete (maximalIdeal R) R] [FaithfulSMul R Ω]
    [∀ i, Module.Finite R (S i)] {π : R} (hπR : Irreducible π)
    (hπ : ∀ i, Irreducible (algebraMap R (S i) π)) :
    HenselianLocalRing (↥(⨆ i, S i)) := by
  have hmax (i : ι) : (maximalIdeal R).map (algebraMap R (S i)) = maximalIdeal (S i) := by
    rw [hπR.maximalIdeal_eq, (hπ i).maximalIdeal_eq, Ideal.map_span, Set.image_singleton]
  let : ∀ i, HenselianLocalRing (S i) := fun i ↦ unramified_stage_henselian (hmax i)
  exact henselianLocalRing_iSup S hS π hπ

end RaynaudParameters
