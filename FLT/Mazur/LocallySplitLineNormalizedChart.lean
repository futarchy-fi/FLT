/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineSectionLineCanonicalPoint
public import FLT.Mazur.LocallySplitLineDualChartCompatibility
public import FLT.Mazur.FiniteFreeChartSectionLines

/-!
# Reverse points of actual normalized ambient chart inclusions

An inclusion-preserving source isomorphism recovers the normalized point.
The statement retains the self-refinement convention of chart line gluing.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace FLT.Mazur.LocallySplitLineAmbientChart
open FCurve SplitLineAffineNeighborhood AffineFreeSheafCoordinates NormalizedSectionLine
open FiniteFreeChartTransitions SplitLineAffinePresentation
variable {X : Scheme.{u}} {L M : X.Modules} (s : L ⟶ M)
variable (hL : LocallyFreeRankOne L) (hs : LocallySplit s)
variable (U : X.Opens) [IsAffine U.toScheme] {ι : Type u} [Finite ι]
variable (e : M.restrict U.ι ≅ SheafOfModules.free ι)
variable (i : ι) (N : Chart Γ(U.toScheme, ⊤) ι i)

/-- A chart line isomorphism identifies the original inclusion in free coordinates. -/
lemma inclusion_sectionLine (a : L.restrict U.ι ≅ sectionLineSheaf U.toScheme i N)
    (ha : a.hom ≫ chartSectionLineInclusion M le_rfl e i N =
      (restrictFunctor U.ι).map s) :
    a.hom ≫ sectionLineInclusion U.toScheme i N =
      inclusion s U (refineChart M le_rfl e) := by
  rw [inclusion, ← ha, Category.assoc]
  simp only [chartSectionLineInclusion, Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- The recovered normalized source line gives exactly its original projective point. -/
lemma point_sectionLine (a : L.restrict U.ι ≅ sectionLineSheaf U.toScheme i N)
    (ha : a.hom ≫ chartSectionLineInclusion M le_rfl e i N =
      (restrictFunctor U.ι).map s) :
    point s hL hs U e = ProjectiveSpace.affineSectionLinePoint (.id _) i N := by
  let r := CategoryTheory.retraction (sectionLineInclusion U.toScheme i N)
  have hr : sectionLineInclusion U.toScheme i N ≫ r = 𝟙 _ := IsSplitMono.id _
  have ht : LocallySplit (sectionLineInclusion U.toScheme i N) := by
    intro x
    exact ⟨⊤, trivial, inferInstance⟩
  rw [← point_refine_self s hL hs U e]
  unfold point
  rw [morphism_sourceIso a _ _ (inclusion_sectionLine s U e i N a ha)
    (hL.restrict U.ι) (sectionLineSheaf_rankOne U.toScheme i N) _ ht]
  exact morphism_sectionLine i N _ ht r hr

end FLT.Mazur.LocallySplitLineAmbientChart
