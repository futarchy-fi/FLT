/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteProjectiveRankFrames

/-!
# Affine covers retaining specified sheaf frames

Pointwise frames on open neighborhoods refine to an actual affine open cover.
The index type of every frame is preserved, so a prescribed rank is retained.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
namespace FLT.Mazur.ModuleSheafFramedAffineCover
universe u
variable {X : Scheme.{u}} (P : X.Modules) (τ : Type u)

/-- Pointwise frames yield a genuine affine open cover with the same specified frame type. -/
theorem exists_affineFrameCover
    (hP : ∀ x : X, ∃ U : X.Opens, x ∈ U ∧
      Nonempty (P.restrict U.ι ≅ SheafOfModules.free τ)) :
    ∃ C : X.AffineOpenCover.{u}, ∀ j,
      Nonempty ((pullback (C.f j)).obj P ≅ SheafOfModules.free τ) := by
  choose U hx e using hP
  have hU : iSup U = ⊤ := by
    apply top_unique
    intro x _
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨x, hx x⟩
  let C := X.openCoverOfIsOpenCover U hU
  refine ⟨C.affineRefinement, ?_⟩
  intro j
  let a := (C.X j.1).affineCover.f j.2
  let e₀ : (pullback (C.f j.1)).obj P ≅ SheafOfModules.free τ :=
    ((restrictFunctorIsoPullback (U j.1).ι).app P).symm ≪≫ (e j.1).some
  exact ⟨((pullbackComp a (C.f j.1)).app P).symm ≪≫
    (pullback a).mapIso e₀ ≪≫ ModuleGlobalEvaluationPullback.freeIso a τ⟩

/-- Actual projective stalk ranks supply prescribed finite frames on an affine cover. -/
theorem finiteProjective_pullback_affineFrameCover
    {R : CommRingCat.{0}} (Q : ModuleCat.{0} R)
    [Module.Finite R Q] [Module.Projective R Q]
    {T : Scheme.{0}} (g : T ⟶ Spec R) (d : ℕ)
    (hd : ∀ x : T, Module.rankAtStalk (R := R) Q (g x) = d) :
    ∃ C : T.AffineOpenCover.{0}, ∀ j,
      Nonempty ((pullback (C.f j)).obj ((pullback g).obj (tilde Q)) ≅
        SheafOfModules.free (Fin d)) :=
  exists_affineFrameCover _ (Fin d)
    (fun x ↦ FCurve.finiteProjective_rank_pullback_frame Q g d x (hd x))

end FLT.Mazur.ModuleSheafFramedAffineCover
