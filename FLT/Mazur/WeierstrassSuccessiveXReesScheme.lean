/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSuccessiveXReesChart
public import FLT.Mazur.BlowupReesProper

/-!
# The successive x-chart inside the proper Rees scheme

The proved fraction-algebra comparison embeds the actual three-generator
scheme into Rees Proj. Its contraction is the preceding divided-chart map.
This supplies one chart of the local step, not a properness claim for that open chart.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

namespace FLT.Mazur.WeierstrassSuccessiveX

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {R : Type*} [CommRing R] [IsDomain R]
  (W : WeierstrassCurve R) (s π b3 b4 b6 : R) (hπ : π ≠ 0)
local notation "B" =>
  WeierstrassDilatation.Coordinate W s (π * b3) (π * b4) (π ^ 2 * b6)
local notation "BX" => WeierstrassDilatation.x W s (π * b3) (π * b4) (π ^ 2 * b6)
local notation "I" => modificationCenter W s π b3 b4 b6

/-- The actual successive x-chart is the horizontal fraction chart as a scheme. -/
def horizontalReesSchemeIso : Spec (.of (Coordinate W s π b3 b4 b6)) ≅
    Spec (.of (horizontalReesChart W s π b3 b4 b6)) :=
  Scheme.Spec.mapIso
    (horizontalReesChartEquiv W s π b3 b4 b6 hπ).symm.toRingEquiv.toCommRingCatIso.op

/-- The actual x-direction chart embeds in the Rees projective spectrum. -/
def toReesProj : Spec (.of (Coordinate W s π b3 b4 b6)) ⟶ BlowupRees.proj I :=
  (horizontalReesSchemeIso W s π b3 b4 b6 hπ).hom ≫
    BlowupRees.fractionChartInclusion I BX (Ideal.subset_span (by simp))

/-- The comparison gives an open immersion of the actual equation chart. -/
instance toReesProj_isOpenImmersion : IsOpenImmersion (toReesProj W s π b3 b4 b6 hπ) := by
  unfold toReesProj
  infer_instance

/-- The Rees embedding retains the original preceding divided contraction. -/
@[reassoc] theorem toReesProj_contraction :
    toReesProj W s π b3 b4 b6 hπ ≫ BlowupRees.contraction I =
      toDivided W s π b3 b4 b6 := by
  rw [toReesProj, Category.assoc, BlowupRees.fractionChartInclusion_contraction]
  change Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro a
  apply (horizontalReesChartEquiv W s π b3 b4 b6 hπ).injective
  change (horizontalReesChartEquiv W s π b3 b4 b6 hπ)
      ((horizontalReesChartEquiv W s π b3 b4 b6 hπ).symm
        (algebraMap B (BlowupFractionChart.chart I BX) a)) = _
  rw [AlgEquiv.apply_symm_apply]
  apply Subtype.ext
  exact (horizontalReesChartEquiv_fromDivided W s π b3 b4 b6 hπ a).symm

omit [IsDomain R] in
/-- The ambient Rees contraction is proper for the actual three-generator center. -/
theorem reesContraction_isProper : IsProper (BlowupRees.contraction I) := by
  apply BlowupRees.contraction_isProper
  exact Submodule.fg_span (Set.toFinite _)

end FLT.Mazur.WeierstrassSuccessiveX
