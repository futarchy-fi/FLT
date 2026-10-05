/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CoefficientModelLimit
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Noetherian

/-!
# Finiteness at every coefficient model stage

Separatedness, quasi-compactness, and local finite presentation persist in
the coefficient inverse system. Each finite coefficient stage is Noetherian,
as is the corresponding scheme model. Under these hypotheses, properness
at a stage is equivalent to the remaining universal-closedness condition.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory Limits AlgebraicGeometry

namespace FLT.Mazur.Approximation

universe u

variable {A : Type u} [CommRing A] {S₀ : Subalgebra ℤ A}
  {Y : Scheme.{u}} (q : Y ⟶ Spec (.of S₀)) (i : (CoefficientStage S₀)ᵒᵖ)

/-- Every finite coefficient ring is Noetherian. -/
theorem coefficientStage_isNoetherianRing : IsNoetherianRing i.unop.val :=
  Algebra.FiniteType.isNoetherianRing ℤ _

/-- The structure map at every enlarged coefficient stage remains separated. -/
theorem coefficientModel_isSeparated [IsSeparated q] :
    IsSeparated (pullback.snd q ((coefficientSpectrumToInitial S₀).app i)) := by
  infer_instance

/-- The structure map at every enlarged coefficient stage remains quasi-compact. -/
theorem coefficientModel_quasiCompact [QuasiCompact q] :
    QuasiCompact (pullback.snd q ((coefficientSpectrumToInitial S₀).app i)) := by
  infer_instance

/-- The structure map at every stage retains local finite presentation. -/
theorem coefficientModel_locallyOfFinitePresentation [LocallyOfFinitePresentation q] :
    LocallyOfFinitePresentation
      (pullback.snd q ((coefficientSpectrumToInitial S₀).app i)) := by
  infer_instance

/-- Every coefficient scheme model of a quasi-compact finite-type morphism is Noetherian. -/
theorem coefficientModel_isNoetherian [QuasiCompact q] [LocallyOfFiniteType q] :
    IsNoetherian ((coefficientModelDiagram S₀ q).obj i) := by
  let := coefficientStage_isNoetherianRing i
  have : IsNoetherian ((coefficientSpectrumDiagram S₀).obj i) := by
    change IsNoetherian (Spec (.of i.unop.val))
    infer_instance
  let qi := pullback.snd q ((coefficientSpectrumToInitial S₀).app i)
  have : IsLocallyNoetherian ((coefficientModelDiagram S₀ q).obj i) :=
    LocallyOfFiniteType.isLocallyNoetherian qi
  have : CompactSpace ((coefficientModelDiagram S₀ q).obj i) :=
    QuasiCompact.compactSpace_of_compactSpace qi
  exact ⟨⟩

/-- For these separated finite-type models, universal closedness is the remaining condition. -/
theorem coefficientModel_isProper_iff [IsSeparated q] [LocallyOfFiniteType q] :
    IsProper (pullback.snd q ((coefficientSpectrumToInitial S₀).app i)) ↔
      UniversallyClosed (pullback.snd q ((coefficientSpectrumToInitial S₀).app i)) := by
  constructor
  · intro h
    let := h
    infer_instance
  · intro h
    let := h
    exact ⟨⟩

end FLT.Mazur.Approximation
