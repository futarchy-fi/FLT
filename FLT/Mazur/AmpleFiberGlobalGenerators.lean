/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ProperLocalAmpleFiberGenerators
public import FLT.Mazur.StalkBaseNumeratorOpen
public import FLT.Mazur.StalkBaseSectionLifting

/-!
# Original global sections covering an ample fiber

Lift a finite affine section cover over the base local ring, then take
global numerators. Unit denominators preserve generator opens, so the
original sections cover the chosen fiber with affine generator opens.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry TopologicalSpace
open Scheme.Modules FLT.Mazur.FCurve ModuleLineBundleTensorPullback

namespace FLT.Mazur.StalkBase

variable {X S : Scheme.{0}} [IsAffine S] [IsLocallyNoetherian S]
  [CompactSpace X] [X.IsSeparated] (f : X ⟶ S) [IsProper f] (s : S)
  {L : X.Modules} (hline : LocallyFreeRankOne L)
  (hL : AmpleLineBundle ((pullback (f.fiberι s)).obj L))

include hline hL

/-- Global sections of a high power cover the chosen ample fiber by affine opens. -/
theorem exists_global_fiber_cover (N : ℕ) :
    ∃ (n : ℕ), N ≤ n ∧ 0 < n ∧ ∃ (ι : Type) (_ : Finite ι)
      (a : ι → Γ(tensorPower L n, ⊤)),
      (∀ i, IsAffineOpen (f.fiberι s ⁻¹ᵁ sectionGeneratorOpen (tensorPower L n) (a i))) ∧
      (∀ x : f.fiber s, ∃ i, f.fiberι s x ∈
        sectionGeneratorOpen (tensorPower L n) (a i)) := by
  let _ := family_isSeparated f s
  obtain ⟨n, hn, hn0, ι, hι, t, haff, hcover⟩ :=
    exists_lifted_closedFiber_cover (projection f s) (hline.pullback (toSource f s))
      ((closedFiber_ample_iff f s L).mpr hL) N
  let e := tensorPowerIso (toSource f s) L n
  let _ := (hline.tensorPower n).isFinitePresentation
  have hnum (i : ι) := exists_section_numerator_open f s (hline.tensorPower n)
    (e.inv.app ⊤ (t i))
  choose a ha using hnum
  have hopen (i : ι) : toSource f s ⁻¹ᵁ sectionGeneratorOpen (tensorPower L n) (a i) =
      sectionGeneratorOpen (tensorPower ((pullback (toSource f s)).obj L) n) (t i) := by
    rw [ha i]
    exact sectionGeneratorOpen_iso e.symm (t i)
  let c := closedFiberIso f s
  have hc : c.inv ≫ (projection f s).fiberι
      (IsLocalRing.closedPoint (S.presheaf.stalk s)) ≫ toSource f s = f.fiberι s := by
    rw [← closedFiberIso_hom_ι, Iso.inv_hom_id_assoc]
  refine ⟨n, hn, hn0, ι, hι, a, ?_, ?_⟩
  · intro i
    have h := (haff i).preimage c.inv
    rw [← hopen i, ← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage,
      Category.assoc, hc] at h
    exact h
  · intro x
    have hx : toSource f s ((projection f s).fiberι
        (IsLocalRing.closedPoint (S.presheaf.stalk s)) (c.inv x)) = f.fiberι s x :=
      congrArg (fun k : f.fiber s ⟶ X ↦ k x) hc
    have hm : (projection f s).fiberι
        (IsLocalRing.closedPoint (S.presheaf.stalk s)) (c.inv x) ∈
        ⨆ i, sectionGeneratorOpen
          (tensorPower ((pullback (toSource f s)).obj L) n) (t i) := by
      rw [hcover]
      trivial
    obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hm
    rw [← hopen i] at hi
    exact ⟨i, hx ▸ hi⟩

end FLT.Mazur.StalkBase
