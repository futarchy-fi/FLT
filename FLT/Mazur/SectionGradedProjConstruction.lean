/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SectionGradedProjGluing

/-!
# The section-ring Proj morphism from positive-power generation

If every point lies in the generator open of some positive tensor-power
section, intersect these opens with actual line trivializations. The local
fraction maps then glue to a scheme morphism into the full section-ring Proj.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
namespace FLT.Mazur.SectionGradedProjConstruction
open FCurve ModuleLineBundleTensorPullback SectionGradedSum SectionGradedProjChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {X : Scheme.{u}} (L : X.Modules) [hL : Fact (LocallyFreeRankOne L)]

/-- Every point admits a generating global section in some positive tensor degree. -/
def PositivePowerGenerated : Prop :=
  ∀ x : X, ∃ (d : ℕ) (_ : 0 < d) (s : Γ(tensorPower L d, ⊤)),
    x ∈ sectionGeneratorOpen (tensorPower L d) s

/-- Positive-power generation gives a genuine trivializing section cover. -/
theorem exists_generating_cover (h : PositivePowerGenerated L) :
    ∃ (𝒰 : X.OpenCover.{u})
      (e : ∀ i, (pullback (𝒰.f i)).obj L ≅ structureModule (𝒰.X i))
      (d : 𝒰.I₀ → ℕ) (s : ∀ i, Γ(tensorPower L (d i), ⊤)),
      (∀ i, 0 < d i) ∧
      ∀ i, IsUnit (SectionGradedProjChart.ringHom (𝒰.f i) L (e i) (of L ⊤ (d i) (s i))) := by
  choose d hd s hs using h
  choose W hW e using hL.out
  let V (x : X) : X.Opens := W x ⊓ sectionGeneratorOpen (tensorPower L (d x)) (s x)
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
  exact ringHom_of_isUnit L (V x) (eV x) (s x) inf_le_right

/-- The actual morphism to Proj of the full tensor-power section ring. -/
def toProj (h : PositivePowerGenerated L) : X ⟶ Proj (grade L ⊤) := by
  let 𝒰 := (exists_generating_cover L h).choose
  let e := (exists_generating_cover L h).choose_spec.choose
  let d := (exists_generating_cover L h).choose_spec.choose_spec.choose
  let s := (exists_generating_cover L h).choose_spec.choose_spec.choose_spec.choose
  let hs := (exists_generating_cover L h).choose_spec.choose_spec.choose_spec.choose_spec
  exact SectionGradedProjGluing.fromCover L 𝒰 e d s hs.1 hs.2

/-- Positive-power generation supplies a scheme morphism with no assumed Proj-map data. -/
theorem nonempty_hom (h : PositivePowerGenerated L) : Nonempty (X ⟶ Proj (grade L ⊤)) :=
  ⟨toProj L h⟩

/-- The morphism agrees with gluing over any genuine trivializing generating cover. -/
lemma toProj_eq_fromCover (h : PositivePowerGenerated L) (𝒰 : X.OpenCover)
    (e : ∀ i, (pullback (𝒰.f i)).obj L ≅ structureModule (𝒰.X i))
    (d : 𝒰.I₀ → ℕ) (s : ∀ i, Γ(tensorPower L (d i), ⊤)) (hd : ∀ i, 0 < d i)
    (hs : ∀ i, IsUnit (SectionGradedProjChart.ringHom
      (𝒰.f i) L (e i) (of L ⊤ (d i) (s i)))) :
    toProj L h = SectionGradedProjGluing.fromCover L 𝒰 e d s hd hs := by
  unfold toProj
  exact SectionGradedProjGluing.fromCover_independent L _ _ _ _ _ _ 𝒰 e d s hd hs

/-- The canonical morphism has the actual homogeneous-fraction formula on every chart. -/
@[reassoc]
lemma toProj_comp (h : PositivePowerGenerated L) {Y : Scheme.{u}} (p : Y ⟶ X)
    (e : (pullback p).obj L ≅ structureModule Y)
    {d : ℕ} (s : Γ(tensorPower L d, ⊤)) (hd : 0 < d)
    (hs : IsUnit (SectionGradedProjChart.ringHom p L e (of L ⊤ d s))) :
    p ≫ toProj L h = SectionGradedProjChart.toProj p L e (of L ⊤ d s) hs ⟨s, rfl⟩ hd := by
  unfold toProj
  exact SectionGradedProjGluing.fromCover_comp L _ _ _ _ _ _ p e s hd hs

/-- On a trivializing generator subopen the canonical map is the constructed chart map. -/
@[reassoc]
lemma toProj_generatorChart (h : PositivePowerGenerated L) (U : X.Opens)
    (e : (pullback U.ι).obj L ≅ structureModule U.toScheme)
    {d : ℕ} (s : Γ(tensorPower L d, ⊤)) (hd : 0 < d)
    (hs : U ≤ sectionGeneratorOpen (tensorPower L d) s) :
    U.ι ≫ toProj L h = generatorChart L U e s hd hs :=
  toProj_comp L h U.ι e s hd (ringHom_of_isUnit L U e s hs)

omit [Fact (LocallyFreeRankOne L)] in
/-- An ample line bundle satisfies the positive-power generation hypothesis. -/
lemma positivePowerGenerated_of_ample (h : AmpleLineBundle L) : PositivePowerGenerated L := by
  intro x
  obtain ⟨d, hd, s, hx, _⟩ := h.2.2 x
  exact ⟨d, hd, s, hx⟩

end FLT.Mazur.SectionGradedProjConstruction
