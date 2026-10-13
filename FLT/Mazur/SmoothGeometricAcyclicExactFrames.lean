/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ProperLineAcyclicExactFrames
public import FLT.Mazur.SmoothAffineLineNoetherianModel

/-!
# Exact-rank actual direct-image frames on unrestricted smooth families

Model descent retains actual fiber ranks as well as acyclicity. Its precise
frames descend to the original sheaf, then assemble without an affine base.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
namespace FLT.Mazur.LineSectionBaseChange
open FCurve CartierAbel
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {X S : Scheme.{0}} (f : X ⟶ S) [IsProper f] [Smooth f]
  (L : X.Modules) (hL : LocallyFreeRankOne L)
  (hV : ∀ s : S, ∀ n, Subsingleton (ModuleH ((pullback (f.fiberι s)).obj L) (n + 1)))

include hL hV in
/-- The actual affine direct image has a frame of the prescribed fiber section dimension. -/
theorem smoothAffine_geometricAcyclic_exactRank_frame [IsAffine S]
    (s : S) (d : ℕ) (hd : properLineFiberSectionRank f L s = d) :
    ∃ U : S.Opens, s ∈ U ∧ Nonempty
      (((pushforward f).obj L).restrict U.ι ≅ SheafOfModules.free (Fin d)) := by
  obtain ⟨Y, B, q, a, b, M, hB, hq, hsm, hM, h, ⟨e⟩⟩ :=
    smoothAffineLine_noetherian_model f L hL
  have hv : ∀ s : S, ∀ n, Subsingleton
      (ModuleH ((pullback (f.fiberι s)).obj ((pullback a).obj M)) (n + 1)) := fun s n ↦
    (Equiv.subsingleton_congr
      (moduleHIsoOfIso ((pullback (f.fiberι s)).mapIso e) (n + 1)).toEquiv).mpr (hV s n)
  have hr := (fiberSectionRank_eq_of_iso f s ((pullback (f.fiberι s)).mapIso e)).trans hd
  obtain ⟨U, hs, ⟨c⟩⟩ := properLineAcyclicBaseChanged_exactRank_frame h M hM hv s d hr
  exact ⟨U, hs, ⟨((restrictFunctor U.ι).mapIso ((pushforward f).mapIso e)).symm ≪≫ c⟩⟩

include hL hV in
/-- The actual direct image has exact-rank frames over every original smooth base. -/
theorem smooth_geometricAcyclic_exactRank_frame
    (s : S) (d : ℕ) (hd : properLineFiberSectionRank f L s = d) :
    ∃ U : S.Opens, s ∈ U ∧ Nonempty
      (((pushforward f).obj L).restrict U.ι ≅ SheafOfModules.free (Fin d)) := by
  obtain ⟨U, hU, hs, _⟩ := exists_isAffineOpen_mem_and_subset
    (U := ⊤) (x := s) (by trivial)
  let _ : IsAffine U.toScheme := hU
  let N := (pullback (f ⁻¹ᵁ U).ι).obj L
  have hv (t : U.toScheme) (n : ℕ) :
      Subsingleton (ModuleH ((pullback ((f ∣_ U).fiberι t)).obj N) (n + 1)) :=
    (properLine_fiber_vanishing_iff (isPullback_morphismRestrict f U).flip
      L hL t (n + 1)).mpr (hV (U.ι t) n)
  have hr := (properLineFiberSectionRank_baseChange
    (isPullback_morphismRestrict f U).flip L hL ⟨s, hs⟩).trans hd
  obtain ⟨V, ht, ⟨e⟩⟩ := smoothAffine_geometricAcyclic_exactRank_frame
    (f ∣_ U) N (hL.pullback _) hv ⟨s, hs⟩ d hr
  exact frame_of_openPullback _ U.ι ⟨s, hs⟩ V ht
    ((restrictFunctor V.ι).mapIso (DirectImageBaseChange.openIso f U L) ≪≫ e)

end FLT.Mazur.LineSectionBaseChange
