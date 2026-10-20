/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ProperOnlyRelativeAmpleFibers
public import FLT.Mazur.AmpleFiberCartesianDescent

/-!
# The actual ample-fiber open of a proper family

The locus is defined by ampleness on the original residue fibers. Neighborhood
and descent theorems prove openness and its exact base-change criterion.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
namespace FLT.Mazur.FCurve
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {X S : Scheme.{0}} (f : X ⟶ S) [IsProper f]
  (L : X.Modules) (hL : LocallyFreeRankOne L)
include hL

omit [IsProper f] in
/-- Relative ampleness gives ampleness on the actual residue-field fiber. -/
theorem RelativeAmple.ample_fiber (ha : RelativeAmple f L) (s : S) :
    AmpleLineBundle ((pullback (f.fiberι s)).obj L) := by
  have hb := ha.baseChange hL (S.fromSpecResidueField s)
  exact (hb.relativelyAmpleLineBundle (hL.pullback _)).ample_of_affine

/-- A cartesian base change preserves and reflects ampleness at corresponding fibers. -/
theorem ample_fiber_iff_of_isPullback {Y T : Scheme.{0}}
    {a : Y ⟶ X} {p : Y ⟶ T} {b : T ⟶ S} (sq : IsPullback a p f b) (t : T) :
    AmpleLineBundle ((pullback (p.fiberι t)).obj ((pullback a).obj L)) ↔
      AmpleLineBundle ((pullback (f.fiberι (b t))).obj L) := by
  let _ : IsProper p := MorphismProperty.of_isPullback sq inferInstance
  let _ : IsProper (p.fiberToSpecResidueField t) := by
    dsimp [Scheme.Hom.fiberToSpecResidueField]
    infer_instance
  constructor
  · intro ha
    have hb := relativeAmple_fiber_of_isPullback sq hL t
      ((ha.relative_of_affine (p.fiberToSpecResidueField t)).relativeAmple)
    exact (hb.relativelyAmpleLineBundle (hL.pullback _)).ample_of_affine
  · exact ampleLineBundle_fiber_of_isPullback sq t L

/-- The set of points where the original divisor line is ample on the residue fiber. -/
def properAmpleFiberLocus : Set S :=
  {s | AmpleLineBundle ((pullback (f.fiberι s)).obj L)}

/-- Fiber ampleness defines an open subset of the original base. -/
theorem properAmpleFiberLocus_isOpen : IsOpen (properAmpleFiberLocus f L) := by
  apply isOpen_iff_mem_nhds.mpr
  intro s hs
  obtain ⟨W, hsW, _, ha⟩ := exists_relativeAmple_neighborhood_proper f s L hL hs
  apply Filter.mem_of_superset (W.isOpen.mem_nhds hsW)
  intro t ht
  have hb := ha.of_iso ((restrictFunctorIsoPullback (f ⁻¹ᵁ W).ι).app L).symm
  have hc := hb.ample_fiber (f ∣_ W) _ (hL.pullback _) (⟨t, ht⟩ : W.toScheme)
  exact (ample_fiber_iff_of_isPullback f L hL
    (isPullback_morphismRestrict f W).flip ⟨t, ht⟩).mp hc

/-- The scheme-theoretic open retaining precisely the original ample fibers. -/
def properAmpleFiberOpen : S.Opens :=
  ⟨properAmpleFiberLocus f L, properAmpleFiberLocus_isOpen f L hL⟩

/-- A cartesian test is relatively ample exactly when its image is in the ample open. -/
theorem relativeAmple_iff_range_ampleFiberOpen {Y T : Scheme.{0}}
    {a : Y ⟶ X} {p : Y ⟶ T} {b : T ⟶ S} (sq : IsPullback a p f b) :
    RelativeAmple p ((pullback a).obj L) ↔
      Set.range b ⊆ properAmpleFiberOpen f L hL := by
  let _ : IsProper p := MorphismProperty.of_isPullback sq inferInstance
  constructor
  · intro ha t ht
    obtain ⟨v, rfl⟩ := ht
    exact (ample_fiber_iff_of_isPullback f L hL sq v).mp
      (ha.ample_fiber p _ (hL.pullback _) v)
  · intro ha
    apply relativeAmple_of_ample_fibers_proper p _ (hL.pullback _)
    intro t
    exact (ample_fiber_iff_of_isPullback f L hL sq t).mpr (ha ⟨t, rfl⟩)

/-- The original line is relatively ample over its constructed ample open. -/
theorem properAmpleFiberOpen_relativeAmple :
    RelativeAmple (f ∣_ properAmpleFiberOpen f L hL)
      ((pullback (f ⁻¹ᵁ properAmpleFiberOpen f L hL).ι).obj L) := by
  apply (relativeAmple_iff_range_ampleFiberOpen f L hL
    (isPullback_morphismRestrict f (properAmpleFiberOpen f L hL)).flip).mpr
  rintro _ ⟨x, rfl⟩
  exact x.property

end FLT.Mazur.FCurve
