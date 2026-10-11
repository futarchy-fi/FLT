/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.TrivializedLineSheafLimitDescent
public import FLT.Mazur.FiniteAffineLineCover

/-!
# Every line bundle descends through a separated affine-transition limit

Descend a finite affine trivializing cover, then its transition cocycle.
The line on the limit is arbitrary: no stage line, stage trivializations,
or preselected model of its class is assumed.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
open FLT.Mazur.FCurve
namespace FLT.Mazur.Approximation
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {I : Type u} [Category.{u} I] [IsCofiltered I]
  (D : I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
  [∀ {i j} (f : i ⟶ j), IsAffineHom (D.map f)]
  [∀ i, (D.obj i).IsSeparated] [∀ i, CompactSpace (D.obj i)]

include hc in
/-- Every independently varying line on the limit is the actual pullback of a stage line. -/
theorem exists_lineSheaf_of_limit (L : c.pt.Modules) (hL : LocallyFreeRankOne L) :
    ∃ (i : I) (M : (D.obj i).Modules), LocallyFreeRankOne M ∧
      Nonempty ((Scheme.Modules.pullback (c.π.app i)).obj M ≅ L) := by
  let _ := Scheme.compactSpace_of_isLimit D c hc
  obtain ⟨ι, hι, U, hU, he, hcover⟩ := hL.finite_affine_trivializing_cover
  let _ := hι
  obtain ⟨i, V, hV, hrec⟩ :=
    Scheme.exists_isOpenCover_and_isAffine_of_finite D c hc U hcover hU
  have hcompact (s : NonemptyChartSet ι) :
      IsCompact (finiteIntersectionOpen V s : Set (D.obj i)) := by
    have ha : IsAffineOpen (finiteIntersectionOpen V s) :=
      finiteIntersectionSchemeDiagram_isAffine V (fun j ↦ (hrec j).1) (.op s)
    exact ha.isCompact
  have heV j : Nonempty (L.restrict (c.π.app i ⁻¹ᵁ V j).ι ≅
      structureModule (c.π.app i ⁻¹ᵁ V j).toScheme) := by
    rw [← (hrec j).2]
    exact he j
  obtain ⟨r, M, hM, e⟩ := exists_trivializedLineSheaf_of_limit D c hc i V hV hcompact L heV
  exact ⟨r.left, M, hM, e⟩

end FLT.Mazur.Approximation
