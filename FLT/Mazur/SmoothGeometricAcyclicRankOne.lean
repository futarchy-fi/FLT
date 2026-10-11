/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SmoothAffineLineNoetherianModel
public import FLT.Mazur.GeometricAcyclicPicardLocality

/-!
# Actual acyclic direct images on unrestricted smooth families

Affine approximation and open base change compute the actual direct image
of every line bundle on a proper smooth family. Neither the base nor the
line bundle is required to come from a supplied Noetherian model.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
namespace FLT.Mazur.CartierAbel
open FCurve LineSectionBaseChange
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {X S : Scheme.{0}} (f : X ⟶ S) [IsProper f] [Smooth f]
  (L : X.Modules) (hL : LocallyFreeRankOne L)

include hL in
/-- On every proper smooth family, the geometric condition computes the actual direct image. -/
theorem smooth_geometricAcyclicRankOne_iff_actual :
    GeometricAcyclicRankOne f L ↔ AcyclicRankOne f L := by
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
      exact ((smoothAffine_geometricAcyclicRankOne_iff_actual
        (f ∣_ U.1) _ (hL.pullback _)).mp ha).2.of_iso
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
      apply (smoothAffine_geometricAcyclicRankOne_iff_actual
        (f ∣_ U.1) _ (hL.pullback _)).mpr
      refine ⟨fun t n ↦ ?_, (hA.2.pullback U.1.ι).of_iso
        (DirectImageBaseChange.openIso f U.1 L)⟩
      exact (properLine_fiber_vanishing_iff (isPullback_morphismRestrict f U.1).flip
        L hL t (n + 1)).mpr (hA.1 (U.1.ι t) n)

end FLT.Mazur.CartierAbel
