/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteTypeAffineIndependentLineModel
public import FLT.Mazur.GeometricAcyclicRankOneLocus

/-!
# Intrinsic acyclic opens for independent lines on arbitrary tests

The original proper flat integral family has a finite-type integer base.
The test and its independently varying line need no finiteness hypotheses.
Affine approximation proves openness locally, and actual open images glue it.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open Scheme.Modules
namespace FLT.Mazur.CartierAbel
open FCurve LineSectionBaseChange
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R]
  {X Y S : Scheme.{0}} {a : X ⟶ Y} {f : X ⟶ S}
  {q : Y ⟶ Spec (.of R)} {g : S ⟶ Spec (.of R)}
  [IsProper q] [Flat q] [GeometricallyIntegral q] (h : IsPullback a f q g)
  (L : X.Modules) (hL : LocallyFreeRankOne L)

include h hL in
/-- On affine tests an independent Noetherian line model proves intrinsic openness. -/
theorem finiteTypeAffine_isOpen_acyclicRankOneLocus [IsAffine S] :
    IsOpen (geometricAcyclicRankOneLocus f L) := by
  obtain ⟨Z, B, r, p, b, M, hB, hr, hflat, hint, hM, H, ⟨e⟩⟩ :=
    Approximation.finiteTypeAffine_independent_line_model h L hL
  rw [← geometricAcyclicRankOneLocus_iso f e,
    geometricAcyclicRankOneLocus_baseChange r H M hM,
    geometricAcyclicRankOneLocus_eq_open r M hM]
  exact (b ⁻¹ᵁ properLineAcyclicRankOneOpen r M hM).isOpen

include h hL in
/-- The independently varying line's exact fiber acyclic rank-one locus is open on every test. -/
theorem finiteTypeTest_isOpen_acyclicRankOneLocus :
    IsOpen (geometricAcyclicRankOneLocus f L) := by
  let _ : IsProper f := MorphismProperty.of_isPullback h inferInstance
  refine isOpen_iff_forall_mem_open.mpr fun s hs ↦ ?_
  obtain ⟨U, hU, hsU, _⟩ := exists_isAffineOpen_mem_and_subset
    (show s ∈ (⊤ : S.Opens) from trivial)
  let _ : IsAffine U.toScheme := hU
  let N := (pullback (f ⁻¹ᵁ U).ι).obj L
  let V : U.toScheme.Opens := ⟨geometricAcyclicRankOneLocus (f ∣_ U) N,
    finiteTypeAffine_isOpen_acyclicRankOneLocus
      ((isPullback_morphismRestrict f U).flip.paste_horiz h) N (hL.pullback _)⟩
  have hv : (V : Set U.toScheme) = U.ι ⁻¹' geometricAcyclicRankOneLocus f L :=
    geometricAcyclicRankOneLocus_baseChange f (isPullback_morphismRestrict f U).flip L hL
  refine ⟨U.ι ''ᵁ V, ?_, (U.ι ''ᵁ V).isOpen, ?_⟩
  · rintro _ ⟨t, ht, rfl⟩
    exact (Set.ext_iff.mp hv t).mp ht
  · exact ⟨⟨s, hsU⟩, (Set.ext_iff.mp hv ⟨s, hsU⟩).mpr hs, rfl⟩

/-- The actual open on an arbitrary test is defined by the intrinsic fiber condition. -/
def finiteTypeTestAcyclicOpen : S.Opens :=
  ⟨geometricAcyclicRankOneLocus f L, finiteTypeTest_isOpen_acyclicRankOneLocus h L hL⟩

end FLT.Mazur.CartierAbel
