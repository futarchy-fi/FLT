/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteTypeAffineIndependentLineModel
public import FLT.Mazur.GeometricAcyclicPicardLocality

/-!
# Actual direct images of all test lines for finite-type original bases

The original family has a finite-type integer base. The test scheme and its
line bundle are unrestricted. Affine approximation computes the actual global
direct image, retaining the original line independently on every chart.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
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
/-- Every line on an affine test has the actual acyclic rank-one direct image criterion. -/
theorem finiteTypeAffine_geometricAcyclicRankOne_iff_actual [IsAffine S] :
    GeometricAcyclicRankOne f L ↔ AcyclicRankOne f L := by
  obtain ⟨Z, B, r, p, b, M, hB, hr, hflat, hint, hM, H, ⟨e⟩⟩ :=
    Approximation.finiteTypeAffine_independent_line_model h L hL
  exact (geometricAcyclicRankOne_iso f e).symm.trans
    ((geometricAcyclicRankOne_iff_actual r H M hM).trans (acyclicRankOne_iso f e))

include h hL in
/-- On every test scheme, fiber geometry computes the actual direct image of every test line. -/
theorem finiteTypeTest_geometricAcyclicRankOne_iff_actual :
    GeometricAcyclicRankOne f L ↔ AcyclicRankOne f L := by
  let _ : IsProper f := MorphismProperty.of_isPullback h inferInstance
  let _ (U : S.affineOpens) : IsAffine U.1.toScheme := U.2
  constructor
  · intro hA
    refine ⟨fun s ↦ (hA s).1, ?_⟩
    apply LocallyFreeRankOne.of_openPullbackCover
      (fun U : S.affineOpens ↦ U.1.toScheme) (fun U : S.affineOpens ↦ U.1.ι)
    · intro s
      obtain ⟨U, hU, hs, _⟩ := exists_isAffineOpen_mem_and_subset
        (U := ⊤) (x := s) (by trivial)
      exact ⟨⟨U, hU⟩, ⟨s, hs⟩, rfl⟩
    · intro U
      have ha := geometricAcyclicRankOne_baseChange f
        (isPullback_morphismRestrict f U.1).flip L hL hA
      exact ((finiteTypeAffine_geometricAcyclicRankOne_iff_actual
        ((isPullback_morphismRestrict f U.1).flip.paste_horiz h) _ (hL.pullback _)).mp ha).2.of_iso
          (DirectImageBaseChange.openIso f U.1 L).symm
  · intro hA
    refine geometricAcyclicRankOne_of_jointlySurjective f
      (fun U : S.affineOpens ↦ (f ⁻¹ᵁ U.1).toScheme)
      (fun U : S.affineOpens ↦ U.1.toScheme)
      (fun U : S.affineOpens ↦ (f ⁻¹ᵁ U.1).ι)
      (fun U : S.affineOpens ↦ f ∣_ U.1) (fun U : S.affineOpens ↦ U.1.ι)
      (fun U ↦ (isPullback_morphismRestrict f U.1).flip) ?_ L hL ?_
    · intro s
      obtain ⟨U, hU, hs, _⟩ := exists_isAffineOpen_mem_and_subset
        (U := ⊤) (x := s) (by trivial)
      exact ⟨⟨U, hU⟩, ⟨s, hs⟩, rfl⟩
    · intro U
      apply (finiteTypeAffine_geometricAcyclicRankOne_iff_actual
        ((isPullback_morphismRestrict f U.1).flip.paste_horiz h) _ (hL.pullback _)).mpr
      refine ⟨fun t n ↦ ?_, (hA.2.pullback U.1.ι).of_iso
        (DirectImageBaseChange.openIso f U.1 L)⟩
      exact (properLine_fiber_vanishing_iff (isPullback_morphismRestrict f U.1).flip
        L hL t (n + 1)).mpr (hA.1 (U.1.ι t) n)

end FLT.Mazur.CartierAbel
