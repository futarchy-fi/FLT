/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCyclicBoundaryStandardContraction
public import FLT.Mazur.PolygonCyclicBoundaryStandardDivisor

/-!
# Canonical contraction lines between chosen standard field polygons

The actual translated contraction pulls the full target marking ideal back to
the original transported source ideal. Its positive-line comparison preserves
the canonical section, with no rescaling or replacement of the divisor.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory
namespace FLT.Mazur.PolygonCyclicBoundary
open PolygonPinching PolygonUniversalAction PolygonMarkingBaseChange FCurve
open CyclicBoundaryParameter
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] PolygonParameterTranslation.translationIso markingIdeal
  PolygonParameterTranslation.movedMarkingIdeal
variable (K L : Type) [Field K] [Field L] [Algebra K L]
local notation "g" => ProjectiveLineProductCharts.parameterToBase K L
local notation "e₁" => PolygonStandardFieldExtension.iso K L 1 (by decide)

/-- The entire original target marking ideal on the independently chosen one-gon. -/
def standardTargetIdeal (a : Kˣ) : (PolygonAtlas.polygon L 1).left.IdealSheafData :=
  (markingIdeal K 1 (PolygonAtlas.normalization K 1) (g) a 0).comap (e₁).hom.left

/-- The chosen one-gon target retains the original relative Cartier marking. -/
theorem standardTargetIdeal_cartier (a : Kˣ) :
    RelativeEffectiveCartier (PolygonAtlas.polygon L 1).hom (standardTargetIdeal K L a) := by
  let v := (Over.forget (Spec (.of L))).mapIso (e₁)
  have hs := markingIdeal_cartier K 1 (by decide) (PolygonAtlas.normalization K 1)
    (PolygonAtlas.nodes K 1) (PolygonAtlas.isPushout K 1 (by decide)) (g) a 0
  have hc := hs.comap_of_isOpenImmersion v.hom
  change RelativeEffectiveCartier ((e₁).hom.left ≫ _) (standardTargetIdeal K L a) at hc
  rw [Over.w] at hc
  exact hc

variable (m : ℕ) [NeZero m] (hm : 0 < m) (n : ℕ) [NeZero n]
  (f : Over.mk (ProjectiveLineProductCharts.parameterToBase K L) ⟶
    CyclicBoundaryParameter.parameter (G K m) n)
  (a : Kˣ) (i : Fin m) (j : Multiplicative (ZMod n))
local notation "e" => PolygonStandardFieldExtension.iso K L m hm

/-- The chosen-standard contraction retains the complete original marked ideal. -/
theorem standardContraction_ideal :
    (standardTargetIdeal K L a).comap (standardContraction K L m hm n f i j).left =
      standardLabelIdeal K L m hm n f a i j := by
  have he := congrArg Over.Hom.left (standardContraction_comparison K L m hm n f i j)
  simp only [Over.comp_left] at he
  rw [standardTargetIdeal, ← Scheme.IdealSheafData.comap_comp, he,
    Scheme.IdealSheafData.comap_comp, extendedContraction_ideal]
  rfl

/-- The canonical positive-line comparison on the actual chosen-standard contraction. -/
irreducible_def standardContractionLine :
    (Scheme.Modules.pullback (standardContraction K L m hm n f i j).left).obj
      (divisorLineBundle (standardTargetIdeal K L a) (standardTargetIdeal_cartier K L a).1) ≅
      divisorLineBundle (standardLabelIdeal K L m hm n f a i j)
        (standardLabelIdeal_cartier K L m hm n f a i j).1 := by
  let hs := (standardTargetIdeal_cartier K L a).1
  let ht := (standardLabelIdeal_cartier K L m hm n f a i j).1
  let he := standardContraction_ideal K L m hm n f a i j
  let _ := idealModulePullbackHom_isIso_of_cartier _ hs (he.symm ▸ ht)
  exact divisorLinePullbackIsoOfEq _ hs ht he

/-- The actual standard contraction preserves the entire marking's canonical section. -/
theorem standardContractionLine_section :
    DivisorLineSectionCompatible (standardContraction K L m hm n f i j).left
      (standardTargetIdeal_cartier K L a).1
      (standardLabelIdeal_cartier K L m hm n f a i j).1
      (standardContractionLine K L m hm n f a i j) := by
  let hs := (standardTargetIdeal_cartier K L a).1
  let ht := (standardLabelIdeal_cartier K L m hm n f a i j).1
  let he := standardContraction_ideal K L m hm n f a i j
  let _ := idealModulePullbackHom_isIso_of_cartier _ hs (he.symm ▸ ht)
  rw [standardContractionLine_def]
  exact divisorLinePullbackIsoOfEq_compatible _ _ _ _

end FLT.Mazur.PolygonCyclicBoundary
