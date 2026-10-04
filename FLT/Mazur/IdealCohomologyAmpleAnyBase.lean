/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ClosedPointLineSection
public import FLT.Mazur.IdealCohomologyAmpleCriterion

/-!
# A cohomological ampleness criterion over an arbitrary base

The reduced subscheme at a closed point has only one point, so its line
sheaves are trivial independently of the base ring. Ideal H¹ vanishing
therefore constructs affine section neighborhoods of every closed point.
Compactness then gives the section-open definition of ampleness.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
open Scheme.Modules

namespace FLT.Mazur.FCurve
open ModuleSheafTensor ModuleLineBundleTensorPullback
open FLT.Mazur.GlobalIdealPower FLT.Mazur.CommonIdealDirectSum
open FLT.Mazur.GlobalIdealPowerCompatibility

variable {X : Scheme.{0}} [IsLocallyNoetherian X] {L : X.Modules}

/-- Ideal-twist H¹ vanishing supplies an affine section neighborhood of every closed point. -/
theorem closedPoint_affine_section_of_ideal_vanishing_anyBase (hL : LocallyFreeRankOne L)
    (hvan : ∀ I : X.IdealSheafData, ∃ n : ℕ, 0 < n ∧
      Subsingleton (ModuleH (tensor (idealModule I) (tensorPower L n)) 1))
    (x : X) (hx : IsClosed ({x} : Set X)) :
    ∃ (n : ℕ), 0 < n ∧ ∃ s : Γ(tensorPower L n, ⊤),
      x ∈ sectionGeneratorOpen (tensorPower L n) s ∧
        IsAffineOpen (sectionGeneratorOpen (tensorPower L n) s) := by
  obtain ⟨U, hxU, hU, ⟨e⟩⟩ := hL.exists_affine_trivialization x
  let I := comparisonIdeal U
  let J := Scheme.IdealSheafData.vanishingIdeal (⟨{x}, hx⟩ : Closeds X)
  have hJs : (J.support : Set X) = {x} := Scheme.IdealSheafData.coe_support_vanishingIdeal _
  have hIJ : I ⊔ J = ⊤ := by
    apply (Scheme.IdealSheafData.support_eq_bot_iff _).mp
    rw [Scheme.IdealSheafData.support_sup]
    apply bot_unique
    intro y hy
    have hyx : y = x := by simpa only [hJs, Set.mem_singleton_iff] using hy.2
    subst y
    exact (show x ∈ I.support.compl from by
      change x ∈ complement (comparisonIdeal U)
      rw [comparisonIdeal_complement]
      exact hxU) hy.1
  obtain ⟨z, _⟩ : ∃ z : J.subscheme, J.subschemeι z = x := by
    apply Set.mem_range.mp
    rw [Scheme.IdealSheafData.range_subschemeι, hJs]
    exact Set.mem_singleton x
  have : Subsingleton J.subscheme := ⟨fun a b ↦ J.subschemeι.isClosedEmbedding.injective (by
    have ha : J.subschemeι a = x := by
      have hm : J.subschemeι a ∈ (J.support : Set X) := J.range_subschemeι ▸ ⟨a, rfl⟩
      simpa [hJs] using hm
    have hb : J.subschemeι b = x := by
      have hm : J.subschemeι b ∈ (J.support : Set X) := J.range_subschemeι ▸ ⟨b, rfl⟩
      simpa [hJs] using hm
    exact ha.trans hb.symm)⟩
  obtain ⟨n, hn, hzero⟩ := hvan (I ⊓ J)
  let P := tensorPower L n
  have hP := hL.tensorPower n
  have := hP.isFinitePresentation
  obtain ⟨et⟩ := (hP.pullback J.subschemeι).trivial_of_subsingleton z
  obtain ⟨t, ht⟩ := exists_ideal_section_generating_trivial_closed I J hIJ hP et
  let s := (scalarAction I P).app ⊤ t
  have hbound : sectionGeneratorOpen P s ≤ U := by
    have h := idealTensor_section_generatorOpen_le I P t
    change sectionGeneratorOpen P s ≤ complement (comparisonIdeal U) at h
    rwa [comparisonIdeal_complement] at h
  let e' : (pullback U.ι).obj L ≅ structureModule U.toScheme :=
    ((restrictFunctorIsoPullback U.ι).app L).symm ≪≫ e
  let ep : P.restrict U.ι ≅ structureModule U.toScheme :=
    (restrictFunctorIsoPullback U.ι).app P ≪≫ tensorPowerIso U.ι L n ≪≫
      tensorPowerTrivialization e' n
  exact ⟨n, hn, s, ht (hJs.symm ▸ Set.mem_singleton x),
    isAffineOpen_sectionGeneratorOpen_of_le hP U hU ep s hbound⟩

/-- On a compact scheme, ideal H¹ vanishing gives actual ampleness without a field base. -/
theorem ampleLineBundle_of_ideal_h1_vanishing_anyBase [CompactSpace X]
    (hL : LocallyFreeRankOne L)
    (hvan : ∀ I : X.IdealSheafData, ∃ n : ℕ, 0 < n ∧
      Subsingleton (ModuleH (tensor (idealModule I) (tensorPower L n)) 1)) :
    AmpleLineBundle L :=
  ampleLineBundle_of_closedPoint_sections hL
    (closedPoint_affine_section_of_ideal_vanishing_anyBase hL hvan)

end FLT.Mazur.FCurve
