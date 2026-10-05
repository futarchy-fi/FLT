/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineLineTwistLocalization
public import FLT.Mazur.AffineOpenCechBoundary
public import FLT.Mazur.FiniteAffineLineCover
public import FLT.Mazur.IdealTwistCohomologySystem
public import FLT.Mazur.SequentialCechLocalization

/-!
# Finite-stage annihilation in the actual section-twist cohomology system

On a compact separated locally Noetherian scheme, a coherent coefficient
sheaf twisted along a line section with affine generator open has every
positive-degree cohomology class killed at a finite stage. The proof uses a
finite affine trivializing cover, actual section denominators, and the
coefficient-natural comparison between Cech and module cohomology.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open Scheme.Modules

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FLT.Mazur.FCurve.LineSectionTwistSystem

open ModuleSheafTensor ModuleLineBundleTensorPullback CechSheafHZero

variable {X : Scheme} [CompactSpace X] [X.IsSeparated] [IsLocallyNoetherian X]
  (M : X.Modules) [M.IsFinitePresentation] {L : X.Modules}
  (hL : LocallyFreeRankOne L) (s : Γ(L, ⊤))
  (hs : IsAffineOpen (sectionGeneratorOpen L s))

include hL hs in
/-- Every positive module cohomology class dies under a finite actual section-twist map. -/
theorem exists_moduleH_annihilator (q n : ℕ)
    (x : ModuleH ((system M s).obj n) (q + 1)) :
    ∃ (m : ℕ) (h : n ≤ m), moduleHMap ((system M s).map (homOfLE h)) (q + 1) x = 0 := by
  classical
  obtain ⟨ι, hι, U, hU, he, hCover⟩ := hL.finite_affine_trivializing_cover
  let := hι
  let e (i : ι) := (he i).some
  let W := sectionGeneratorOpen L s
  let A := system M s
  let B := A ⋙ restrictFunctor W.ι ⋙ pushforward W.ι
  let a : A ⟶ B := Functor.whiskerLeft A (restrictAdjunction W.ι).unit
  let F := A ⋙ SheafOfModules.toSheaf X.ringCatSheaf
  let G := B ⋙ SheafOfModules.toSheaf X.ringCatSheaf
  let b : F ⟶ G := Functor.whiskerRight a (SheafOfModules.toSheaf X.ringCatSheaf)
  have hF (r : ℕ) : (A.obj r).IsQuasicoherent := by
    have := (hL.tensorPower r).isFinitePresentation
    have := FLT.Mazur.GlobalIdealPower.tensor_coherent M (tensorPower L r)
    change (tensor M (tensorPower L r)).IsQuasicoherent
    infer_instance
  let := hF
  have hExact (r : ℕ) :
      ((SequentialCechLocalization.complexes U G).obj r).ExactAt (q + 1) := by
    exact (HomologicalComplex.exactAt_iff_isZero_homology _ _).mpr
      (AddCommGrpCat.isZero_iff_subsingleton.mpr
        (AffineOpenCechBoundary.cech_subsingleton W hs (A.obj r) U hU hCover
          (q + 1) (by omega)))
  have hLift (v : Fin (q + 1) → ι) (r : ℕ)
      (z : (G.obj r).obj.obj (Opposite.op (V U q v))) :
      ∃ (m : ℕ) (h : r ≤ m) (c : (F.obj m).obj.obj (Opposite.op (V U q v))),
        (b.app m).hom.app (Opposite.op (V U q v)) c =
          (G.map (homOfLE h)).hom.app (Opposite.op (V U q v)) z := by
    obtain ⟨d, t, ht⟩ := exists_affine_stage_lift M hL s (V U q v)
      (affineCover_intersection_isAffineOpen U hU q v) (tupleLineTrivialization U e q v) r z
    exact ⟨r + d, Nat.le_add_right r d, t, ht⟩
  have hKill (v : Fin (q + 2) → ι) (r : ℕ)
      (z : (F.obj r).obj.obj (Opposite.op (V U (q + 1) v)))
      (hz : (b.app r).hom.app (Opposite.op (V U (q + 1) v)) z = 0) :
      ∃ (m : ℕ) (h : r ≤ m),
        (F.map (homOfLE h)).hom.app (Opposite.op (V U (q + 1) v)) z = 0 := by
    obtain ⟨d, hd⟩ := exists_affine_stage_annihilator M hL s (V U (q + 1) v)
      (affineCover_intersection_isAffineOpen U hU (q + 1) v)
      (tupleLineTrivialization U e (q + 1) v) r z hz
    exact ⟨r + d, Nat.le_add_right r d, hd⟩
  let c := (affineCoverCechEquiv (A.obj n) U hU hCover (q + 1)).symm x
  obtain ⟨m, h, hm⟩ := SequentialCechLocalization.homology_annihilator U F G b q
    hExact hLift hKill n c
  refine ⟨m, h, ?_⟩
  have hn := affineCoverCechEquiv_naturality (A.obj n) U hU hCover
    (A.map (homOfLE h)) (q + 1) c
  have hc : affineCoverCechEquiv (A.obj n) U hU hCover (q + 1) c = x :=
    (affineCoverCechEquiv (A.obj n) U hU hCover (q + 1)).apply_symm_apply x
  rw [hc] at hn
  exact hn.symm.trans ((congrArg (affineCoverCechEquiv (A.obj m) U hU hCover (q + 1)) hm).trans
    (map_zero _))

include hL hs in
/-- The field-linear system has the same finite-stage annihilation property. -/
theorem exists_cohomology_annihilator {k : Type} [Field k]
    (f : X ⟶ Spec (CommRingCat.of k)) (q n : ℕ) (x : (cohomology f M s (q + 1)).obj n) :
    ∃ (m : ℕ) (h : n ≤ m), (cohomology f M s (q + 1)).map (homOfLE h) x = 0 :=
  exists_moduleH_annihilator M hL s hs q n x

end FLT.Mazur.FCurve.LineSectionTwistSystem
