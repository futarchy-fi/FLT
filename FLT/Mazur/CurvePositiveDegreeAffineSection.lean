/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CurvePositiveDegreeSections
public import FLT.Mazur.IdealTwistSectionOpen
public import FLT.Mazur.AffineTrivialLineSectionOpen

/-!
# A nonzero positive-power section with affine generator open

Choose an affine trivializing neighborhood of the generic point. Twisting by
the ideal of its complement imposes vanishing there without changing the
positive Euler-characteristic slope. A nonzero section then has generator open
inside the chosen chart, where it is a principal affine open.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open Scheme.Modules

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FLT.Mazur.FCurve

open ModuleLineBundleTensorPullback FLT.Mazur.GlobalIdealPower
open FLT.Mazur.CommonIdealDirectSum FLT.Mazur.GlobalIdealPowerCompatibility

variable {k : Type} [Field k] {X : Scheme} [IsIntegral X]
  (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]
  (hd : topologicalKrullDim X ≤ 1)

include hd in
/-- Positive degree gives a nonzero section of a positive power with affine nonvanishing open. -/
theorem exists_nonzero_line_power_affine_section {L : X.Modules}
    (hL : LocallyFreeRankOne L) (hdeg : 0 < curveSheafDegree f L) :
    ∃ (n : ℕ), 0 < n ∧ ∃ s : Γ(tensorPower L n, ⊤),
      s ≠ 0 ∧ IsAffineOpen (sectionGeneratorOpen (tensorPower L n) s) := by
  have := Chow.source_isNoetherian f
  obtain ⟨U, hx, hU, ⟨e⟩⟩ := hL.exists_affine_trivialization (genericPoint X)
  let I := comparisonIdeal U
  have hI : I ≠ ⊥ := by
    simpa only [pow_one] using comparisonIdeal_power_ne_bot U _ hx 1
  obtain ⟨n, hn, t, ht⟩ := exists_nonzero_ideal_line_power_section f hd I hI hL hdeg
  let P := tensorPower L n
  have hP := hL.tensorPower n
  have := hP.isFinitePresentation
  have := scalarAction_mono I hP
  let s : Γ(P, ⊤) := (scalarAction I P).app ⊤ t
  have hs : s ≠ 0 := by
    intro hz
    apply ht
    apply ModuleSubobjectCoverEquality.app_injective (scalarAction I P) ⊤
    simpa only [map_zero] using hz
  have hbound : sectionGeneratorOpen P s ≤ U := by
    have h := idealTensor_section_generatorOpen_le I P t
    change sectionGeneratorOpen P s ≤ complement (comparisonIdeal U) at h
    rwa [comparisonIdeal_complement] at h
  let e' : (pullback U.ι).obj L ≅ structureModule U.toScheme :=
    ((restrictFunctorIsoPullback U.ι).app L).symm ≪≫ e
  let ep : P.restrict U.ι ≅ structureModule U.toScheme :=
    (restrictFunctorIsoPullback U.ι).app P ≪≫ tensorPowerIso U.ι L n ≪≫
      tensorPowerTrivialization e' n
  exact ⟨n, hn, s, hs, isAffineOpen_sectionGeneratorOpen_of_le hP U hU ep s hbound⟩

end FLT.Mazur.FCurve
