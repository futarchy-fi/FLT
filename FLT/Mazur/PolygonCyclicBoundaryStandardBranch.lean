/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCyclicBoundaryStandardComponentLine
public import FLT.Mazur.PolygonCyclicBoundaryStandardNodeLine

/-!
# Original branch maps in specified standard boundary coordinates

The projective-line and point coefficient comparisons retain each original
branch and its full endpoint ideal. The resulting endpoint comparison is the
canonical section-preserving one.
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
local notation "z" => ProjectiveLineFieldExtension.pointIso K L
local notation "F" => Over.pullback (g)
variable (l : Fin m) (s : point K ⟶ component K) (t : point L ⟶ component L)
  (w : s ≫ (componentι K m k ≫ PolygonAtlas.normalization K m) =
    nodeι K m l ≫ PolygonAtlas.nodes K m)
  (vst : t ≫ (ProjectiveLineFieldExtension.componentIso K L).hom =
    (ProjectiveLineFieldExtension.pointIso K L).hom ≫
      (Over.pullback (ProjectiveLineProductCharts.parameterToBase K L)).map s)

include w vst in
/-- The specified coefficient comparisons retain the full translated branch incidence. -/
theorem standardComponent_node :
    t.left ≫ (standardComponent K L m hm n f j k).left =
      (standardNode K L m hm n f j l).left := by
  have he : t ≫ standardComponent K L m hm n f j k =
      standardNode K L m hm n f j l := by
    apply (cancel_mono (e).hom).mp
    rw [Category.assoc, standardComponent_comparison, ← Category.assoc, vst,
      Category.assoc, standardNode_comparison]
    congr 1
    apply Over.OverMorphism.ext
    exact extendedComponent_node K L m hm (p) (q) (h) n f j k l s w
  exact congrArg Over.Hom.left he

include hm w vst in
/-- The entire original standard component ideal is the unit ideal at either endpoint. -/
theorem standardNormalizationEndpoint_ideal :
    (standardNormalizationIdeal K L m a i k).comap t.left = ⊤ := by
  have hv := congrArg Over.Hom.left vst
  simp only [Over.comp_left] at hv
  rw [standardNormalizationIdeal, ← Scheme.IdealSheafData.comap_comp, hv,
    Scheme.IdealSheafData.comap_comp,
    normalizationEndpoint_baseChange_ideal K m hm (p) (q) (h) (g) a i k l s w,
    Scheme.IdealSheafData.comap_top]

/-- The canonical endpoint comparison on the specified standard component. -/
irreducible_def standardNormalizationEndpointLine :
    (Scheme.Modules.pullback t.left).obj
      (divisorLineBundle (standardNormalizationIdeal K L m a i k)
        (standardNormalizationIdeal_cartier K L m hm a i k)) ≅
      divisorLineBundle ⊤ effectiveCartier_top := by
  let hs := standardNormalizationIdeal_cartier K L m hm a i k
  let he := standardNormalizationEndpoint_ideal K L m hm a i k l s t w vst
  let _ := idealModulePullbackHom_isIso_of_cartier _ hs (he.symm ▸ effectiveCartier_top)
  exact divisorLinePullbackIsoOfEq _ hs effectiveCartier_top he

/-- The standard endpoint comparison retains the exact canonical section. -/
theorem standardNormalizationEndpointLine_section :
    DivisorLineSectionCompatible t.left (standardNormalizationIdeal_cartier K L m hm a i k)
      effectiveCartier_top (standardNormalizationEndpointLine K L m hm a i k l s t w vst) := by
  let hs := standardNormalizationIdeal_cartier K L m hm a i k
  let he := standardNormalizationEndpoint_ideal K L m hm a i k l s t w vst
  let _ := idealModulePullbackHom_isIso_of_cartier _ hs (he.symm ▸ effectiveCartier_top)
  rw [standardNormalizationEndpointLine_def]
  exact divisorLinePullbackIsoOfEq_compatible _ _ _ _

/-- The endpoint line square retains the original coefficient-point frame exactly. -/
theorem standardNormalizationEndpointLine_square :
    LinePullbackSquare t.left (v).hom.left (z).hom.left ((F).map s).left
      (congrArg Over.Hom.left vst)
      (standardComponentLineComparison K L m hm a i k)
      (standardNormalizationEndpointLine K L m hm a i k l s t w vst)
      (normalizationEndpointLineIso K m hm (p) (q) (h) (g) a i k l s w)
      (divisorEmptyLinePullbackIso (z).hom.left) :=
  divisorLineSectionCompatible_square _ _ _ _ _
    (standardComponentLineComparison_section K L m hm a i k)
    (standardNormalizationEndpointLine_section K L m hm a i k l s t w vst)
    (normalizationEndpointLineIso_section K m hm (p) (q) (h) (g) a i k l s w)
    (divisorEmptyLinePullbackIso_section _)

end FLT.Mazur.PolygonCyclicBoundary
