/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AmpleAmbientHilbertClassification

/-!
# Simultaneous affine ambient support for finitely many Hilbert parameters

A finite union of full finite fibers has finite ambient support. Proper
ampleness puts this entire union in one original affine ambient chart.
This concerns the ambient of the families, not affineness of its Hilbert scheme.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open FLT.Mazur.ClosedIdealCover FLT.Mazur.FCurve
namespace FLT.Mazur.HilbertChart
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] {Z : Scheme} (z : Z ⟶ Spec (.of R)) [IsProper z]
  {L : Z.Modules} (hL : AmpleLineBundle L) (d : ℕ)
  {X : Scheme} (s : X ⟶ Spec (.of R)) (J : RelativeIdealFamilies z d s)

omit [IsProper z] in
/-- All ambient support points above a finite set of original parameters form a finite set. -/
theorem finite_parameter_support (t : Set X) (ht : t.Finite) :
    (⋃ x ∈ t, relativeIdealFiberSupport z d s J x).Finite :=
  ht.biUnion (fun x _ ↦ relativeIdealFiberSupport_finite z d s J x)

include hL in
/-- One original affine ambient contains every full fiber over finitely many parameters. -/
theorem exists_common_affine_fiber_support (t : Set X) (ht : t.Finite) :
    ∃ U : (allAffineAmbientCharts z).Index, ∀ x ∈ t,
      relativeIdealFiberSupport z d s J x ⊆ ((allAffineAmbientCharts z).chart U).opensRange := by
  obtain ⟨n, _, ⟨p⟩⟩ := hL.exists_power_presentation z
  obtain ⟨U, hU⟩ := ProjectiveSpace.exists_affineOpen_of_closed_embedding p.embedding
    (⋃ x ∈ t, relativeIdealFiberSupport z d s J x) (finite_parameter_support z d s J t ht)
  refine ⟨U, fun x hx y hy ↦ ?_⟩
  rw [allAffineAmbientCharts_opensRange]
  exact hU (Set.mem_iUnion₂.mpr ⟨x, hx, hy⟩)

include hL in
/-- The exact support locus of one affine ambient contains all the specified parameters. -/
theorem exists_common_affine_support_open (t : Set X) (ht : t.Finite) :
    ∃ U : (allAffineAmbientCharts z).Index,
      t ⊆ relativeIdealFamilySupportOpen z d s J
        ((allAffineAmbientCharts z).chart U).opensRange := by
  obtain ⟨U, hU⟩ := exists_common_affine_fiber_support z hL d s J t ht
  refine ⟨U, fun x hx ↦ ?_⟩
  exact (mem_relativeIdealFamilySupportOpen z d s J _ x).mpr
    ((relativeIdealFiberSupport_subset_iff z d s J x _).mp (hU x hx))

end FLT.Mazur.HilbertChart
