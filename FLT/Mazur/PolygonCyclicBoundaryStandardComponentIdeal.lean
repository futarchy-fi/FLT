/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCyclicBoundaryStandardNormalization
public import FLT.Mazur.PolygonCyclicBoundaryStandardLabelLine
public import FLT.Mazur.PolygonCyclicBoundaryFieldIdeals

/-!
# Original component marking ideals in specified standard coordinates

Pull the original normalization ideal through the specified projective-line
coefficient isomorphism. The translated standard component recovers this exact
ideal, independently of the cyclic translation label.
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
/-- The full original normalization marking ideal in the specified standard coordinates. -/
def standardNormalizationIdeal : (component L).left.IdealSheafData :=
  (((PolygonMarkedSections.sectionMap K m (p) a i).ker.comap
    (componentι K m k ≫ (p)).left).comap (pullback.fst (component K).hom (g))).comap (v).hom.left

include hm in
/-- The specified component-coordinate comparison retains effective Cartierness. -/
theorem standardNormalizationIdeal_cartier :
    EffectiveCartier (standardNormalizationIdeal K L m a i k) := by
  let vi := (Over.forget (Spec (.of L))).mapIso (v)
  exact (relativeCartierBaseChange (component K).hom (g) _
    (normalizationIdeal_relativeCartier K m hm (p) (q) (h) a i k)).1.comap_of_isOpenImmersion vi.hom

/-- The original component line under the specified projective-line coefficient comparison. -/
irreducible_def standardComponentLineComparison :
    (Scheme.Modules.pullback (v).hom.left).obj
      (normalizationMarkingLine K m hm (p) (q) (h) a i k (g)) ≅
        divisorLineBundle (standardNormalizationIdeal K L m a i k)
          (standardNormalizationIdeal_cartier K L m hm a i k) :=
  divisorLinePullbackIsoOfCartier _ (relativeCartierBaseChange (component K).hom (g) _
    (normalizationIdeal_relativeCartier K m hm (p) (q) (h) a i k)).1
    (standardNormalizationIdeal_cartier K L m hm a i k)

/-- The component-coordinate comparison preserves the original canonical section. -/
theorem standardComponentLineComparison_section :
    DivisorLineSectionCompatible (v).hom.left (relativeCartierBaseChange (component K).hom (g) _
    (normalizationIdeal_relativeCartier K m hm (p) (q) (h) a i k)).1
      (standardNormalizationIdeal_cartier K L m hm a i k)
      (standardComponentLineComparison K L m hm a i k) := by
  rw [standardComponentLineComparison_def]
  exact divisorLinePullbackIsoOfCartier_section _ _ _

/-- The actual translated standard component retains the entire original marking ideal. -/
theorem standardComponent_ideal :
    (standardLabelIdeal K L m hm n f a i j).comap
      (standardComponent K L m hm n f j k).left =
        standardNormalizationIdeal K L m a i k := by
  have he := congrArg Over.Hom.left (standardComponent_comparison K L m hm n f j k)
  simp only [Over.comp_left] at he
  rw [standardLabelIdeal, ← Scheme.IdealSheafData.comap_comp, he,
    Scheme.IdealSheafData.comap_comp, extendedComponent_ideal]
  rfl

end FLT.Mazur.PolygonCyclicBoundary
