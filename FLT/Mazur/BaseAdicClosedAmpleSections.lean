/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.BaseAdicCohomologySeparated
public import FLT.Mazur.BaseAdicFiniteSectionLifting
public import FLT.Mazur.IdealAdicClosedAmpleVanishing
public import FLT.Mazur.IdealAdicLineTower

/-!
# Lifting closed-fiber sections over a Noetherian base

Ampleness on the actual closed source supplies a single twist bound. Proper
formal functions lift every section on every
finite thickening to an actual global section of the original line power.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry
open Scheme.Modules FLT.Mazur.BaseAdicThickening FLT.Mazur.FCurve
open FLT.Mazur.IdealAdicQuotient FLT.Mazur.IdealAdicGradedPullback
open ModuleLineBundleTensorPullback

namespace FLT.Mazur.BaseAdicCohomology

variable {R : CommRingCat.{0}} [IsNoetherianRing R]
  {X : Scheme.{0}} [X.IsSeparated] (f : X ⟶ Spec R) [IsProper f] (J : Ideal R)
  {L : X.Modules} (hline : LocallyFreeRankOne L)
  (hL : AmpleLineBundle ((pullback ((baseIdeal R J).comap f).subschemeι).obj L))

include hline hL

/-- All sufficiently large line powers lift every actual infinitesimal section globally. -/
theorem projectionLine_sections_uniform_surjective_of_closed :
    let _ := Chow.source_isNoetherian f
    ∃ N : ℕ, ∀ m ≥ N, ∀ n : ℕ,
      let _ := (hline.tensorPower m).isFinitePresentation
      Function.Surjective ((projection ((baseIdeal R J).comap f) (tensorPower L m) n).app ⊤) := by
  let _ := Chow.source_isNoetherian f
  obtain ⟨N, hN⟩ := gradedLine_uniform_serreBound_of_closed (baseIdeal R J) f hline hL
  refine ⟨N, fun m hm n ↦ ?_⟩
  let _ := (hline.tensorPower m).isFinitePresentation
  exact projection_sections_surjective_of_graded_vanishing_noetherian f J (tensorPower L m)
    (fun k ↦ hN m hm k 0) n

/-- Large powers lift sections on the actual closed subschemes by canonical pullback. -/
theorem pullGlobalLine_uniform_surjective_of_closed :
    let _ := Chow.source_isNoetherian f
    ∃ N : ℕ, ∀ m ≥ N, ∀ n : ℕ,
      Function.Surjective
        (pullGlobal (((baseIdeal R J).comap f) ^ n).subschemeι (tensorPower L m)) := by
  let _ := Chow.source_isNoetherian f
  obtain ⟨N, hN⟩ := projectionLine_sections_uniform_surjective_of_closed f J hline hL
  refine ⟨N, fun m hm n s ↦ ?_⟩
  let _ := (hline.tensorPower m).isFinitePresentation
  let I := (baseIdeal R J).comap f
  let e := lineQuotientClosedIso I (tensorPower L m) (hline.tensorPower m) n
  obtain ⟨t, ht⟩ := hN m hm n (e.inv.app ⊤ s)
  refine ⟨t, ?_⟩
  have he := congrArg (fun g ↦ g.app ⊤ t)
    (projection_lineQuotientClosedIso I (tensorPower L m) (hline.tensorPower m) n)
  change e.hom.app ⊤ ((projection I (tensorPower L m) n).app ⊤ t) =
    pullGlobal (I ^ n).subschemeι (tensorPower L m) t at he
  rw [← he, ht]
  exact ConcreteCategory.congr_hom (congrArg (fun g ↦ g.app ⊤) e.inv_hom_id) s

/-- Formal vanishing gives actual vanishing when the base ideal lies in the Jacobson radical. -/
theorem line_uniform_cohomology_vanishing_of_closed (hJ : J ≤ Ideal.jacobson ⊥) :
    let _ := Chow.source_isNoetherian f
    ∃ N : ℕ, ∀ m ≥ N, ∀ q : ℕ, Subsingleton (ModuleH (tensorPower L m) (q + 1)) := by
  let _ := Chow.source_isNoetherian f
  obtain ⟨N, hN⟩ := quotientLine_uniform_serreBound_of_closed (baseIdeal R J) f hline hL
  refine ⟨N, fun m hm q ↦ ?_⟩
  let _ := (hline.tensorPower m).isFinitePresentation
  exact cohomology_subsingleton_of_quotients f J (tensorPower L m) hJ (q + 1)
    (fun n ↦ hN m hm n q)

end FLT.Mazur.BaseAdicCohomology
