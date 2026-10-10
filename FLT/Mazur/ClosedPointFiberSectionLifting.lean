/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.BaseAdicClosedAmpleSections
public import FLT.Mazur.ClosedPointFiberAmple
public import FLT.Mazur.ModuleGlobalSectionIso

/-!
# Actual section lifting from an ample closed-point fiber

Over a Noetherian affine base, properness and ampleness on a closed-point
fiber give global lifts of all sufficiently high-power fiber sections.
Over a local base the same hypothesis kills positive cohomology in high degree.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry
open Scheme.Modules FLT.Mazur.FCurve FLT.Mazur.BaseAdicThickening
open ModuleLineBundleTensorPullback

namespace FLT.Mazur.BaseAdicCohomology

variable {R : CommRingCat.{0}} [IsNoetherianRing R]
  {X : Scheme.{0}} [X.IsSeparated] (f : X ⟶ Spec R) [IsProper f]
  (p : Spec R) [p.asIdeal.IsMaximal] {L : X.Modules}
  (hline : LocallyFreeRankOne L) (hL : AmpleLineBundle ((pullback (f.fiberι p)).obj L))

include hline hL

/-- Ample closed-point fibers give a single lifting bound for every infinitesimal thickening. -/
theorem pullGlobalLine_uniform_surjective_of_fiber :
    let _ := Chow.source_isNoetherian f
    ∃ N : ℕ, ∀ m ≥ N, ∀ n : ℕ,
      Function.Surjective
        (pullGlobal (((baseIdeal R p.asIdeal).comap f) ^ n).subschemeι (tensorPower L m)) := by
  exact pullGlobalLine_uniform_surjective_of_closed f p.asIdeal hline
    ((closedSource_ample_iff_fiber p f L).mpr hL)

/-- Actual high-power fiber sections lift to global sections on the proper total space. -/
theorem fiber_sections_uniform_surjective :
    ∃ N : ℕ, ∀ m ≥ N,
      Function.Surjective (pullGlobal (f.fiberι p) (tensorPower L m)) := by
  let _ := Chow.source_isNoetherian f
  obtain ⟨N, hN⟩ := pullGlobalLine_uniform_surjective_of_fiber f p hline hL
  refine ⟨N, fun m hm ↦ ?_⟩
  apply pullGlobal_surjective_of_comp_iso (closedSourceFiberIso R p f).hom
  apply (pullGlobal_surjective_congr (closedSourceFiberIso_hom_ι R p f) _).mpr
  have he := congrArg (fun I : X.IdealSheafData ↦
    Function.Surjective (pullGlobal I.subschemeι (tensorPower L m)))
      (pow_one ((baseIdeal R p.asIdeal).comap f))
  exact he.mp (hN m hm 1)

omit hL [p.asIdeal.IsMaximal] in
/-- Over a local base, an ample closed fiber forces eventual positive cohomology vanishing. -/
theorem line_uniform_cohomology_vanishing_of_closedPoint [IsLocalRing R]
    (hL : AmpleLineBundle ((pullback (f.fiberι (IsLocalRing.closedPoint R))).obj L)) :
    let _ := Chow.source_isNoetherian f
    ∃ N : ℕ, ∀ m ≥ N, ∀ q : ℕ, Subsingleton (ModuleH (tensorPower L m) (q + 1)) := by
  let _ : (IsLocalRing.closedPoint R).asIdeal.IsMaximal :=
    inferInstanceAs (IsLocalRing.maximalIdeal R).IsMaximal
  exact line_uniform_cohomology_vanishing_of_closed f (IsLocalRing.maximalIdeal R) hline
    ((closedSource_ample_iff_fiber (IsLocalRing.closedPoint R) f L).mpr hL)
    (IsLocalRing.maximalIdeal_le_jacobson ⊥)

end FLT.Mazur.BaseAdicCohomology
