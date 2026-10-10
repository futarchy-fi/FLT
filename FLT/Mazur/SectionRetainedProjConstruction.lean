/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SectionRetainedProjGluing
public import FLT.Mazur.AmpleRetainedSectionCover

/-!
# The canonical retained section-ring Proj morphism

Positive generation in the retained tensor degrees constructs a genuine
trivializing cover. Its original section evaluations glue to the retained
Proj map; ampleness supplies this generation for every positive step.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Scheme.Modules

universe u

namespace FLT.Mazur.SectionRetainedProjConstruction

open FCurve ModuleLineBundleTensorPullback SectionGradedSum
open SectionRetainedChartComparison

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {X : Scheme.{u}} (L : X.Modules) [hL : Fact (LocallyFreeRankOne L)] (q : ℕ)

/-- Original positive retained sections generate at every point of the original scheme. -/
def PositivePowerGenerated : Prop :=
  ∀ x : X, ∃ (d : ℕ) (_ : 0 < d) (s : Γ(tensorPower L (q * d), ⊤)),
    x ∈ sectionGeneratorOpen (tensorPower L (q * d)) s

/-- Retained generation supplies an actual trivializing open cover and unit section coordinates. -/
theorem exists_generating_cover (h : PositivePowerGenerated L q) :
    ∃ (𝒰 : X.OpenCover.{u})
      (e : ∀ i, (pullback (𝒰.f i)).obj L ≅ structureModule (𝒰.X i))
      (d : 𝒰.I₀ → ℕ) (s : ∀ i, Γ(tensorPower L (q * d i), ⊤)),
      (∀ i, 0 < d i) ∧ ∀ i, IsUnit (SectionGradedProjChart.ringHom
        (𝒰.f i) L (e i) (of L ⊤ (q * d i) (s i))) := by
  choose d hd s hs using h
  choose W hW e using hL.out
  let V (x : X) : X.Opens := W x ⊓ sectionGeneratorOpen (tensorPower L (q * d x)) (s x)
  have hV : iSup V = ⊤ := by
    apply top_unique
    intro x _
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨x, hW x, hs x⟩
  let 𝒰 := X.openCoverOfIsOpenCover V hV
  let eV (x : X) : (pullback (V x).ι).obj L ≅ structureModule (V x).toScheme :=
    ((restrictFunctorIsoPullback (V x).ι).app L).symm ≪≫
      ModuleSheafTensor.restrictTrivialization (show V x ≤ W x from inf_le_left) (e x).some
  refine ⟨𝒰, eV, d, s, hd, ?_⟩
  intro x
  exact SectionGradedProjChart.ringHom_of_isUnit L (V x) (eV x) (s x) inf_le_right

omit [Fact (LocallyFreeRankOne L)] in
/-- Ampleness supplies positive retained generation for every positive step. -/
theorem positivePowerGenerated_of_ample (hA : AmpleLineBundle L) (hq : 0 < q) :
    PositivePowerGenerated L q := by
  obtain ⟨I, _, d, hd, s, _, hcover⟩ := hA.retained_section_cover q hq
  intro x
  have hx : x ∈ ⨆ i, sectionGeneratorOpen (tensorPower L (q * d)) (s i) := by
    rw [hcover]
    trivial
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
  exact ⟨d, hd, s i, hi⟩

variable [GradedRing (RetainedSubringGrading.grade (grade L ⊤) q)]

/-- The canonical morphism from the original scheme to its retained section-ring Proj. -/
def toProj (h : PositivePowerGenerated L q) :
    X ⟶ Proj (RetainedSubringGrading.grade (grade L ⊤) q) := by
  let 𝒰 := (exists_generating_cover L q h).choose
  let e := (exists_generating_cover L q h).choose_spec.choose
  let d := (exists_generating_cover L q h).choose_spec.choose_spec.choose
  let s := (exists_generating_cover L q h).choose_spec.choose_spec.choose_spec.choose
  let hs := (exists_generating_cover L q h).choose_spec.choose_spec.choose_spec.choose_spec
  exact SectionRetainedProjGluing.fromCover L q 𝒰 e d s hs.1 hs.2

/-- The canonical morphism retains each original invertible retained section chart. -/
@[reassoc]
theorem toProj_comp (h : PositivePowerGenerated L q) {Y : Scheme} (p : Y ⟶ X)
    (e : (pullback p).obj L ≅ structureModule Y)
    {d : ℕ} (s : Γ(tensorPower L (q * d), ⊤)) (hd : 0 < d)
    (hs : IsUnit (SectionGradedProjChart.ringHom p L e (of L ⊤ (q * d) s))) :
    p ≫ toProj L q h = SectionRetainedProjChart.toProj p L e q
      (insertion L q d s) hs (insertion_mem L q d s) hd := by
  unfold toProj
  exact SectionRetainedProjGluing.fromCover_comp L q _ _ _ _ _ _ p e s hd hs

end FLT.Mazur.SectionRetainedProjConstruction
