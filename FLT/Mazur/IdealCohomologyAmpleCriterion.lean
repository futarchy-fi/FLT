/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteClosedIdealSection
public import FLT.Mazur.FiniteSupportClosedDescent
public import FLT.Mazur.CurvePositiveDegreeAffineSection

/-!
# Ideal-cohomology criterion for ampleness over a field

For each closed point, intersect its ideal with the ideal of the complement
of an affine trivializing neighborhood. H¹ vanishing lifts a generator on
the finite closed point to an ideal-twisted section. Its generator open is
contained in that affine chart and is affine. Compactness then upgrades the
closed-point cover to a cover of the whole scheme.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open Scheme.Modules

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FLT.Mazur.FCurve

open ModuleSheafTensor ModuleLineBundleTensorPullback
open FLT.Mazur.GlobalIdealPower FLT.Mazur.CommonIdealDirectSum
open FLT.Mazur.GlobalIdealPowerCompatibility

variable {k : Type} [Field k] {X : Scheme}
  (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f] {L : X.Modules}

include f in
/-- Ideal-twist H¹ vanishing supplies an affine section neighborhood of every closed point. -/
theorem closedPoint_affine_section_of_ideal_vanishing (hL : LocallyFreeRankOne L)
    (hvan : ∀ I : X.IdealSheafData, ∃ n : ℕ, 0 < n ∧
      Subsingleton (ModuleH (tensor (idealModule I) (tensorPower L n)) 1))
    (x : X) (hx : IsClosed ({x} : Set X)) :
    ∃ (n : ℕ), 0 < n ∧ ∃ s : Γ(tensorPower L n, ⊤),
      x ∈ sectionGeneratorOpen (tensorPower L n) s ∧
        IsAffineOpen (sectionGeneratorOpen (tensorPower L n) s) := by
  have := Chow.source_isNoetherian f
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
  have : IsFinite (J.subschemeι ≫ f) :=
    finiteClosed_of_finite_support f J (hJs ▸ Set.finite_singleton x)
  obtain ⟨n, hn, hzero⟩ := hvan (I ⊓ J)
  let P := tensorPower L n
  have hP := hL.tensorPower n
  have := hP.isFinitePresentation
  obtain ⟨t, ht⟩ := exists_ideal_section_generating_finite f I J hIJ hP
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

/-- Affine positive-power section opens covering closed points cover a compact scheme. -/
theorem ampleLineBundle_of_closedPoint_sections [CompactSpace X]
    (hL : LocallyFreeRankOne L)
    (h : ∀ x : X, IsClosed ({x} : Set X) →
      ∃ (n : ℕ), 0 < n ∧ ∃ s : Γ(tensorPower L n, ⊤),
        x ∈ sectionGeneratorOpen (tensorPower L n) s ∧
          IsAffineOpen (sectionGeneratorOpen (tensorPower L n) s)) : AmpleLineBundle L := by
  classical
  refine ⟨inferInstance, hL, fun x ↦ ?_⟩
  let V : X.Opens := ⨆ n : ℕ, ⨆ s : Γ(tensorPower L n, ⊤),
    ⨆ (_ : 0 < n), ⨆ (_ : IsAffineOpen (sectionGeneratorOpen (tensorPower L n) s)),
      sectionGeneratorOpen (tensorPower L n) s
  have hx : x ∈ V := by
    by_contra hx
    obtain ⟨y, hy, hyclosed⟩ := V.isOpen.isClosed_compl.exists_closed_singleton ⟨x, hx⟩
    obtain ⟨n, hn, s, hys, hs⟩ := h y hyclosed
    exact hy (Opens.mem_iSup.mpr ⟨n, Opens.mem_iSup.mpr ⟨s,
      Opens.mem_iSup.mpr ⟨hn, Opens.mem_iSup.mpr ⟨hs, hys⟩⟩⟩⟩)
  obtain ⟨n, hx⟩ := Opens.mem_iSup.mp hx
  obtain ⟨s, hx⟩ := Opens.mem_iSup.mp hx
  obtain ⟨hn, hx⟩ := Opens.mem_iSup.mp hx
  obtain ⟨hs, hx⟩ := Opens.mem_iSup.mp hx
  exact ⟨n, hn, s, hx, hs⟩

include f in
/-- Vanishing for each ideal at some positive power implies actual section-open ampleness. -/
theorem ampleLineBundle_of_ideal_h1_vanishing (hL : LocallyFreeRankOne L)
    (hvan : ∀ I : X.IdealSheafData, ∃ n : ℕ, 0 < n ∧
      Subsingleton (ModuleH (tensor (idealModule I) (tensorPower L n)) 1)) :
    AmpleLineBundle L := by
  have := Chow.source_isNoetherian f
  exact ampleLineBundle_of_closedPoint_sections hL
    (closedPoint_affine_section_of_ideal_vanishing f hL hvan)

end FLT.Mazur.FCurve
