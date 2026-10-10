/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteProjectiveTildeLocal

/-!
# Compatible finite free charts

Finite free charts refine to every contained open. On a common refinement,
the induced change of coordinates satisfies the identity, inverse and cocycle
laws. Compactness supplies a finite cover of actual free charts.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open Scheme.Modules
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
universe u
namespace FLT.Mazur.FiniteFreeChartTransitions
open FCurve
variable {X : Scheme.{u}} (M : X.Modules)

/-- Restrict a genuine free chart to any smaller open, preserving its free coordinates. -/
def refineChart {U V : X.Opens} (h : V ≤ U) {ι : Type u}
    (e : M.restrict U.ι ≅ SheafOfModules.free ι) :
    M.restrict V.ι ≅ SheafOfModules.free ι :=
  (restrictFunctorCongr (X.homOfLE_ι h).symm).app M ≪≫
    (restrictFunctorComp (X.homOfLE h) U.ι).app M ≪≫
    (restrictFunctor (X.homOfLE h)).mapIso e ≪≫
    (restrictFunctorIsoPullback (X.homOfLE h)).app _ ≪≫
    ModuleGlobalEvaluationPullback.freeIso (X.homOfLE h) ι

/-- Change of finite free coordinates on a specified common refinement. -/
def transition {U V W : X.Opens} (hU : W ≤ U) (hV : W ≤ V)
    {ι κ : Type u} (e : M.restrict U.ι ≅ SheafOfModules.free ι)
    (d : M.restrict V.ι ≅ SheafOfModules.free κ) :
    (SheafOfModules.free ι : W.toScheme.Modules) ≅ SheafOfModules.free κ :=
  (refineChart M hU e).symm ≪≫ refineChart M hV d

/-- A chart's own coordinate change is the identity on every smaller open. -/
lemma transition_self {U W : X.Opens} (h : W ≤ U) {ι : Type u}
    (e : M.restrict U.ι ≅ SheafOfModules.free ι) :
    transition M h h e e = Iso.refl _ := by
  ext
  simp [transition]

/-- Reversing a coordinate change gives its actual inverse. -/
lemma transition_symm {U V W : X.Opens} (hU : W ≤ U) (hV : W ≤ V)
    {ι κ : Type u} (e : M.restrict U.ι ≅ SheafOfModules.free ι)
    (d : M.restrict V.ι ≅ SheafOfModules.free κ) :
    (transition M hU hV e d).symm = transition M hV hU d e := rfl

/-- The three coordinate changes on any triple refinement satisfy the cocycle law. -/
lemma transition_cocycle {U V T W : X.Opens} (hU : W ≤ U) (hV : W ≤ V) (hT : W ≤ T)
    {ι κ ν : Type u} (e : M.restrict U.ι ≅ SheafOfModules.free ι)
    (d : M.restrict V.ι ≅ SheafOfModules.free κ)
    (c : M.restrict T.ι ≅ SheafOfModules.free ν) :
    transition M hU hV e d ≪≫ transition M hV hT d c = transition M hU hT e c := by
  ext
  simp [transition]

/-- A compact scheme admits a finite covering family of the constructed free charts. -/
theorem exists_finite_free_cover [CompactSpace X] (hM : LocallyFiniteFree M) :
    ∃ (I : Type u) (_ : Finite I) (U : I → X.Opens) (ι : I → Type u),
      IsOpenCover U ∧ ∀ i, Finite (ι i) ∧
        Nonempty (M.restrict (U i).ι ≅ SheafOfModules.free (ι i)) := by
  choose U hx ι hι e using hM
  have hcover : IsOpenCover U := by
    apply top_le_iff.mp
    intro x _
    exact Opens.mem_iSup.mpr ⟨x, hx x⟩
  obtain ⟨s, hs⟩ := hcover.exists_finite_of_compactSpace
  exact ⟨s, inferInstance, fun i ↦ U i, fun i ↦ ι i, hs, fun i ↦ ⟨hι i, e i⟩⟩

end FLT.Mazur.FiniteFreeChartTransitions
