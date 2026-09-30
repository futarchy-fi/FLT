/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CoherentRestriction
public import FLT.Mazur.ProjectiveSpaceCharts
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-!
# Finite generators on standard projective charts

For an arbitrary locally finitely presented sheaf on polynomial projective
space, each standard affine restriction is tilde of its actual finite module
of sections. These sections yield a finite free epimorphism on each chart.
This is the local input to extending generators after twisting.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory
open FLT.Mazur.FCurve

universe u v

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace FLT.Mazur.ProjectiveSpace

attribute [local instance] MvPolynomial.gradedAlgebra

section

variable (R : Type u) [CommRing R] (ι : Type v)

/-- The standard affine chart as an open immersion from its coordinate spectrum. -/
def chartMap (i : ι) : Spec (.of (chartRing R ι i)) ⟶ space R ι :=
  (chartIso R ι i).inv ≫ (chart R ι i).ι

instance chartMap_isOpenImmersion (i : ι) : IsOpenImmersion (chartMap R ι i) := by
  dsimp [chartMap]
  infer_instance

end

variable (R : Type u) [CommRing R] (ι : Type u)

/-- The original sheaf, restricted to the standard coordinate spectrum. -/
abbrev chartModule (F : (space R ι).Modules) (i : ι) :
    (Spec (.of (chartRing R ι i))).Modules := F.restrict (chartMap R ι i)

/-- Actual global sections on the coordinate spectrum, with its coordinate-ring action. -/
abbrev chartSections (F : (space R ι).Modules) (i : ι) : ModuleCat (chartRing R ι i) :=
  moduleSpecΓFunctor.obj (chartModule R ι F i)

/-- Standard affine restrictions retain local finite presentation. -/
theorem chartModule_isFinitePresentation (F : (space R ι).Modules)
    [F.IsFinitePresentation] (i : ι) : (chartModule R ι F i).IsFinitePresentation :=
  coherent_restrict (chartMap R ι i) F

/-- The actual module of sections on each standard affine chart is finite. -/
theorem chartModule_finite (F : (space R ι).Modules) [F.IsFinitePresentation] (i : ι) :
    Module.Finite (chartRing R ι i) (chartSections R ι F i) :=
  coherent_affineChart_finite (chartMap R ι i) F

/-- The canonical tilde comparison uses the chart sections of the original sheaf. -/
def chartModuleIso (F : (space R ι).Modules) [F.IsFinitePresentation] (i : ι) :
    chartModule R ι F i ≅ tilde (chartSections R ι F i) :=
  coherentAffineChartIso (chartMap R ι i) F

/-- Finite section generators exist on every standard chart, without any chosen
module presentation among the hypotheses. -/
theorem chartModule_generators (F : (space R ι).Modules) [F.IsFinitePresentation] (i : ι) :
    ∃ (n : ℕ) (s : Fin n → chartSections R ι F i),
      Submodule.span (chartRing R ι i) (Set.range s) = ⊤ := by
  have := chartModule_finite R ι F i
  exact Module.Finite.exists_fin (R := chartRing R ι i)

/-- The finite generators give an actual finite free epimorphism on a chart. -/
theorem chartModule_exists_free_epi (F : (space R ι).Modules)
    [F.IsFinitePresentation] (i : ι) :
    ∃ (n : ℕ) (p : SheafOfModules.free (ULift.{u} (Fin n)) ⟶ chartModule R ι F i), Epi p := by
  obtain ⟨n, s, hs⟩ := chartModule_generators R ι F i
  let g : ModuleCat.of (chartRing R ι i) (ULift.{u} (Fin n) →₀ chartRing R ι i) ⟶
      chartSections R ι F i :=
    ModuleCat.ofHom (Y := chartSections R ι F i) (Finsupp.linearCombination (chartRing R ι i)
      (M := chartSections R ι F i) (s ∘ ULift.down))
  have hs' : Submodule.span (chartRing R ι i)
      (Set.range (s ∘ ULift.down : ULift.{u} (Fin n) → _)) = ⊤ := by
    have hr : Set.range (s ∘ ULift.down : ULift.{u} (Fin n) → _) = Set.range s := by
      ext x
      constructor
      · rintro ⟨j, rfl⟩
        exact ⟨j.down, rfl⟩
      · rintro ⟨j, rfl⟩
        exact ⟨ULift.up j, rfl⟩
    rw [hr]
    exact hs
  have : Epi g := (ModuleCat.epi_iff_surjective g).mpr
    ((span_range_eq_top_iff_surjective_finsuppLinearCombination _).mp hs')
  have : Limits.PreservesColimitsOfSize.{u, u}
      (tilde.functor (.of (chartRing R ι i))) :=
    tilde.adjunction.leftAdjoint_preservesColimits
  have : Epi ((tilde.functor (.of (chartRing R ι i))).map g) := inferInstance
  exact ⟨n, (tildeFinsupp (ULift.{u} (Fin n))).inv ≫ (tilde.functor _).map g ≫
    (chartModuleIso R ι F i).inv, inferInstance⟩

/-- Choosing finite generators on every chart gives one finite family when the
coordinate index is finite. The span assertion is over each chart's own ring. -/
theorem finite_chart_generators [Finite ι] (F : (space R ι).Modules)
    [F.IsFinitePresentation] :
    ∃ (n : ι → ℕ) (s : ∀ i, Fin (n i) → chartSections R ι F i),
      Finite (Σ i, Fin (n i)) ∧
        ∀ i, Submodule.span (chartRing R ι i) (Set.range (s i)) = ⊤ := by
  choose n s hs using chartModule_generators R ι F
  exact ⟨n, s, inferInstance, hs⟩

end FLT.Mazur.ProjectiveSpace
