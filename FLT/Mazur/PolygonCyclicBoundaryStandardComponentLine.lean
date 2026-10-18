/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCyclicBoundaryStandardComponentIdeal

/-!
# Exact normalization line squares on the chosen standard polygon

The actual translated standard component comparison preserves the original
canonical section. The line square commutes with both specified coefficient
isomorphisms and the intrinsic extension-field normalization line.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory
namespace FLT.Mazur.PolygonCyclicBoundary
open PolygonPinching PolygonUniversalAction CyclicBoundaryParameter
open PolygonMarkingBaseChange FCurve
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (K L : Type) [Field K] [Field L] [Algebra K L]
  (m : ℕ) [NeZero m] (hm : 0 < m) (n : ℕ) [NeZero n]
  (f : Over.mk (ProjectiveLineProductCharts.parameterToBase K L) ⟶
    CyclicBoundaryParameter.parameter (G K m) n)
  (a : Kˣ) (i : Fin m) (j : Multiplicative (ZMod n)) (k : Fin m)
local notation "p" => PolygonAtlas.normalization K m
local notation "q" => PolygonAtlas.nodes K m
local notation "h" => PolygonAtlas.isPushout K m hm
local notation "e" => PolygonStandardFieldExtension.iso K L m hm

local notation "g" => ProjectiveLineProductCharts.parameterToBase K L
local notation "v" => ProjectiveLineFieldExtension.componentIso K L

/-- The original marking line on each actual translated standard component. -/
irreducible_def standardNormalizationLine :
    (Scheme.Modules.pullback (standardComponent K L m hm n f j k).left).obj
      (divisorLineBundle (standardLabelIdeal K L m hm n f a i j)
        (standardLabelIdeal_cartier K L m hm n f a i j).1) ≅
      divisorLineBundle (standardNormalizationIdeal K L m a i k)
        (standardNormalizationIdeal_cartier K L m hm a i k) := by
  let hs := (standardLabelIdeal_cartier K L m hm n f a i j).1
  let ht := standardNormalizationIdeal_cartier K L m hm a i k
  let he := standardComponent_ideal K L m hm n f a i j k
  let _ := idealModulePullbackHom_isIso_of_cartier _ hs (he.symm ▸ ht)
  exact divisorLinePullbackIsoOfEq _ hs ht he

/-- The standard normalization comparison preserves the entire canonical section. -/
theorem standardNormalizationLine_section :
    DivisorLineSectionCompatible (standardComponent K L m hm n f j k).left
      (standardLabelIdeal_cartier K L m hm n f a i j).1
      (standardNormalizationIdeal_cartier K L m hm a i k)
      (standardNormalizationLine K L m hm n f a i j k) := by
  let hs := (standardLabelIdeal_cartier K L m hm n f a i j).1
  let ht := standardNormalizationIdeal_cartier K L m hm a i k
  let he := standardComponent_ideal K L m hm n f a i j k
  let _ := idealModulePullbackHom_isIso_of_cartier _ hs (he.symm ▸ ht)
  rw [standardNormalizationLine_def]
  exact divisorLinePullbackIsoOfEq_compatible _ _ _ _

/-- The original component line square commutes with both specified coefficient maps. -/
theorem standardNormalizationLine_square :
    LinePullbackSquare (standardComponent K L m hm n f j k).left (e).hom.left
      (v).hom.left (extendedComponent K L m hm (p) (q) (h) n f j k).left
      (congrArg Over.Hom.left (standardComponent_comparison K L m hm n f j k))
      (standardLabelLineComparison K L m hm n f a i j)
      (standardNormalizationLine K L m hm n f a i j k)
      (extendedNormalizationLine K L m hm (p) (q) (h) n f a i j k)
      (standardComponentLineComparison K L m hm a i k) :=
  divisorLineSectionCompatible_square _ _ _ _ _
    (standardLabelLineComparison_section K L m hm n f a i j)
    (standardNormalizationLine_section K L m hm n f a i j k)
    (extendedNormalizationLine_section K L m hm (p) (q) (h) n f a i j k)
    (standardComponentLineComparison_section K L m hm a i k)

end FLT.Mazur.PolygonCyclicBoundary
