/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.LineSheafLimitDescent
public import FLT.Mazur.CoefficientModelRecovery

/-!
# Descending arbitrary lines while keeping the original family model

Only the line bundle varies. The descended total space remains an actual
base change of the original model. Consequently its properness, flatness,
and geometric integrality are retained without a new geometric descent theorem.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
open Scheme.Modules
namespace FLT.Mazur.Approximation
open FCurve
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {A : Type u} [CommRing A] (R : Subalgebra ℤ A) [Algebra.FiniteType ℤ R]
  {Y : Scheme.{u}} (q : Y ⟶ Spec (.of R)) [IsSeparated q] [QuasiCompact q]

/-- Every line on the arbitrary-ring pullback descends to a base change of the fixed model. -/
theorem exists_coefficient_independent_line
    (L : (pullback q (Spec.map (CommRingCat.ofHom R.val.toRingHom))).Modules)
    (hL : LocallyFreeRankOne L) :
    ∃ (i : (CoefficientStage R)ᵒᵖ) (M : ((coefficientModelDiagram R q).obj i).Modules),
      LocallyFreeRankOne M ∧
        Nonempty ((Scheme.Modules.pullback ((coefficientModelCone R q).π.app i)).obj M ≅ L) := by
  let _ (i : (CoefficientStage R)ᵒᵖ) : ((coefficientSpectrumDiagram R).obj i).IsSeparated :=
    inferInstanceAs (Spec (.of i.unop.val)).IsSeparated
  let _ (i : (CoefficientStage R)ᵒᵖ) : ((coefficientModelDiagram R q).obj i).IsSeparated :=
    ⟨by
      change IsSeparated (terminal.from (pullback q ((coefficientSpectrumToInitial R).app i)))
      rw [← terminal.comp_from (pullback.snd q ((coefficientSpectrumToInitial R).app i))]
      infer_instance⟩
  let _ (i : (CoefficientStage R)ᵒᵖ) :
      CompactSpace ((coefficientSpectrumDiagram R).obj i) :=
    inferInstanceAs (CompactSpace (Spec (.of i.unop.val)))
  let _ (i : (CoefficientStage R)ᵒᵖ) : CompactSpace ((coefficientModelDiagram R q).obj i) :=
    QuasiCompact.compactSpace_of_compactSpace
      (pullback.snd q ((coefficientSpectrumToInitial R).app i))
  exact exists_lineSheaf_of_limit (coefficientModelDiagram R q) (coefficientModelCone R q)
    (coefficientModelIsLimit R q) L hL

variable {X : Scheme.{u}} {a : X ⟶ Y} {f : X ⟶ Spec (.of A)}
  (h : IsPullback a f q (Spec.map (CommRingCat.ofHom R.val.toRingHom)))

omit [Algebra.FiniteType ℤ R] [IsSeparated q] [QuasiCompact q] in
/-- The recovery through an arbitrary original cartesian square is the canonical limit leg. -/
lemma coefficientModelRecovery_eq_limit_leg (i : (CoefficientStage R)ᵒᵖ) :
    coefficientModelRecovery h i = h.isoPullback.hom ≫ (coefficientModelCone R q).π.app i := by
  apply pullback.hom_ext <;>
    simp [coefficientModelRecovery, coefficientModelCone, schemeBaseChangeCone]

include h in
/-- A line on any cartesian test descends without changing its original geometric model. -/
theorem exists_coefficient_independent_line_cartesian (L : X.Modules) (hL : LocallyFreeRankOne L) :
    ∃ (i : (CoefficientStage R)ᵒᵖ) (M : ((coefficientModelDiagram R q).obj i).Modules),
      LocallyFreeRankOne M ∧
        Nonempty ((Scheme.Modules.pullback (coefficientModelRecovery h i)).obj M ≅ L) := by
  obtain ⟨i, M, hM, ⟨e⟩⟩ := exists_coefficient_independent_line R q
    ((Scheme.Modules.pullback h.isoPullback.inv).obj L) (hL.pullback _)
  refine ⟨i, M, hM, ⟨?_⟩⟩
  exact (pullbackCongr (coefficientModelRecovery_eq_limit_leg R q h i)).app M ≪≫
    ((pullbackComp h.isoPullback.hom ((coefficientModelCone R q).π.app i)).app M).symm ≪≫
    (Scheme.Modules.pullback h.isoPullback.hom).mapIso e ≪≫
    (pullbackComp h.isoPullback.hom h.isoPullback.inv).app L ≪≫
    (pullbackCongr h.isoPullback.hom_inv_id).app L ≪≫ (pullbackId X).app L

end FLT.Mazur.Approximation
