/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCyclicBoundaryStandardComponentIdeal

/-!
# Exact node frames on the chosen standard polygon

The specified point coefficient map carries the intrinsic node frame to the
actual standard node. Its full ideal is the unit ideal, and both the line
square and the unit-section equation hold without a scalar ambiguity.
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
local notation "v" => ProjectiveLineFieldExtension.pointIso K L

/-- The entire standard marking ideal restricts to the unit ideal at each original node. -/
theorem standardNode_ideal :
    (standardLabelIdeal K L m hm n f a i j).comap
      (standardNode K L m hm n f j k).left = ⊤ := by
  have he := congrArg Over.Hom.left (standardNode_comparison K L m hm n f j k)
  simp only [Over.comp_left] at he
  rw [standardLabelIdeal, ← Scheme.IdealSheafData.comap_comp, he,
    Scheme.IdealSheafData.comap_comp, extendedNode_ideal, Scheme.IdealSheafData.comap_top]

/-- The canonical frame on the actual translated node of the chosen standard polygon. -/
irreducible_def standardNodeFrame :
    (Scheme.Modules.pullback (standardNode K L m hm n f j k).left).obj
      (divisorLineBundle (standardLabelIdeal K L m hm n f a i j)
        (standardLabelIdeal_cartier K L m hm n f a i j).1) ≅
      divisorLineBundle ⊤ effectiveCartier_top := by
  let hs := (standardLabelIdeal_cartier K L m hm n f a i j).1
  let he := standardNode_ideal K L m hm n f a i j k
  let _ := idealModulePullbackHom_isIso_of_cartier _ hs (he.symm ▸ effectiveCartier_top)
  exact divisorLinePullbackIsoOfEq _ hs effectiveCartier_top he

/-- The standard node frame preserves the full canonical section. -/
theorem standardNodeFrame_section :
    DivisorLineSectionCompatible (standardNode K L m hm n f j k).left
      (standardLabelIdeal_cartier K L m hm n f a i j).1 effectiveCartier_top
      (standardNodeFrame K L m hm n f a i j k) := by
  let hs := (standardLabelIdeal_cartier K L m hm n f a i j).1
  let he := standardNode_ideal K L m hm n f a i j k
  let _ := idealModulePullbackHom_isIso_of_cartier _ hs (he.symm ▸ effectiveCartier_top)
  rw [standardNodeFrame_def]
  exact divisorLinePullbackIsoOfEq_compatible _ _ _ _

/-- The specified polygon and point comparisons commute on the exact original node frame. -/
theorem standardNodeFrame_square :
    LinePullbackSquare (standardNode K L m hm n f j k).left (e).hom.left
      (v).hom.left (extendedNode K L m hm (p) (q) (h) n f j k).left
      (congrArg Over.Hom.left (standardNode_comparison K L m hm n f j k))
      (standardLabelLineComparison K L m hm n f a i j)
      (standardNodeFrame K L m hm n f a i j k)
      (extendedNodeFrame K L m hm (p) (q) (h) n f a i j k)
      (divisorEmptyLinePullbackIso (v).hom.left) :=
  divisorLineSectionCompatible_square _ _ _ _ _
    (standardLabelLineComparison_section K L m hm n f a i j)
    (standardNodeFrame_section K L m hm n f a i j k)
    (extendedNodeFrame_section K L m hm (p) (q) (h) n f a i j k)
    (divisorEmptyLinePullbackIso_section _)

/-- The actual standard node frame has unit section exactly. -/
@[reassoc] theorem standardNodeFrame_unit :
    (Scheme.Modules.pullback (standardNode K L m hm n f j k).left).map
        (divisorSectionMap (standardLabelIdeal_cartier K L m hm n f a i j).1) ≫
      (standardNodeFrame K L m hm n f a i j k).hom ≫
        (divisorLineBundleTopIso effectiveCartier_top).hom =
          (modulePullbackUnitIso (standardNode K L m hm n f j k).left).hom :=
  (standardNodeFrame_section K L m hm n f a i j k).unit _

end FLT.Mazur.PolygonCyclicBoundary
