/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OrderedHilbertBaseOpenChart

/-!
# The scheme-chart inverse image is an actual open subscheme

Compare the full constructed intersection with the independently represented
chart-test intersection by their universal lifting properties. The scheme
isomorphism retains both endpoints and proves the original source map open.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.OrderedHilbertBaseOpenChart
open HilbertChart CartierAbel SchemePicard FCurve
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R] {X : Scheme}
  (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  (d : ℕ) (V : Over (Spec (.of R)))
  (c : (relativeFppfSheaf f).obj.obj (op V))
local notation "Z" => variableHilbertTest f d V
local notation "sZ" => variableChartSection f hL d V c
local notation "U" => OrderedHilbertIdentityOriginalSection.sourceTest f hL
local notation "sU" => OrderedHilbertIdentityOriginalSection.sourceSection f hL
local notation "I" => variableHilbertOverlap f d V c U sU
local notation "u" => variableHilbertOverlapToTest f d V c U sU
local notation "v" => variableHilbertOverlapToChart f d hL V c U sU

/-- Reverse the two roles in the same full represented Picard intersection. -/
def toChartIntersection : source f hL d V c ⟶ I :=
  (variableHilbertOverlap_lift f d hL V c U sU
    (inclusion f hL d V c) (projection f hL d V c) (by
      rw [← variableChartSection_map]
      exact (original_class f hL d V c).symm)).choose

/-- Recover the full constructed-source intersection from the chart-test presentation. -/
def fromChartIntersection : I ⟶ source f hL d V c :=
  (OrderedHilbertOriginalTestIntersection.lift f hL Z sZ u v (by
    rw [variableChartSection_map, variableHilbertOverlap_class])).choose

@[reassoc]
theorem toChartIntersection_inclusion :
    toChartIntersection f hL d V c ≫ u = inclusion f hL d V c :=
  (variableHilbertOverlap_lift f d hL V c U sU _ _ (by
    rw [← variableChartSection_map]
    exact (original_class f hL d V c).symm)).choose_spec.1.1

@[reassoc]
theorem toChartIntersection_projection :
    toChartIntersection f hL d V c ≫ v = projection f hL d V c :=
  (variableHilbertOverlap_lift f d hL V c U sU _ _ (by
    rw [← variableChartSection_map]
    exact (original_class f hL d V c).symm)).choose_spec.1.2

@[reassoc]
theorem fromChartIntersection_inclusion :
    fromChartIntersection f hL d V c ≫ inclusion f hL d V c = u :=
  (OrderedHilbertOriginalTestIntersection.lift f hL Z sZ u v (by
    rw [variableChartSection_map, variableHilbertOverlap_class])).choose_spec.1.1

@[reassoc]
theorem fromChartIntersection_projection :
    fromChartIntersection f hL d V c ≫ projection f hL d V c = v :=
  (OrderedHilbertOriginalTestIntersection.lift f hL Z sZ u v (by
    rw [variableChartSection_map, variableHilbertOverlap_class])).choose_spec.1.2

/-- Both full scheme intersections are the same, including their structure sheaves. -/
def chartIntersectionIso : source f hL d V c ≅ I where
  hom := toChartIntersection f hL d V c
  inv := fromChartIntersection f hL d V c
  hom_inv_id := by
    apply OrderedHilbertOriginalTestIntersection.hom_ext f hL Z sZ
    · change (_ ≫ _) ≫ inclusion f hL d V c = (𝟙 _) ≫ inclusion f hL d V c
      rw [Category.assoc, fromChartIntersection_inclusion,
        toChartIntersection_inclusion, Category.id_comp]
    · change (_ ≫ _) ≫ projection f hL d V c = (𝟙 _) ≫ projection f hL d V c
      rw [Category.assoc, fromChartIntersection_projection,
        toChartIntersection_projection, Category.id_comp]
  inv_hom_id := by
    apply variableHilbertOverlap_hom_ext f d hL V c U sU
    · rw [Category.assoc, toChartIntersection_inclusion,
        fromChartIntersection_inclusion, Category.id_comp]
    · rw [Category.assoc, toChartIntersection_projection,
        fromChartIntersection_projection, Category.id_comp]

variable [IsOpenImmersion V.hom]

/-- The constructed full inverse image is an actual open subscheme of the original source. -/
instance inclusion_isOpenImmersion : IsOpenImmersion (inclusion f hL d V c).left := by
  have h := congrArg Over.Hom.left (toChartIntersection_inclusion f hL d V c)
  rw [← h]
  let _ : IsIso (toChartIntersection f hL d V c).left :=
    inferInstanceAs (IsIso ((Over.forget _).mapIso (chartIntersectionIso f hL d V c)).hom)
  change IsOpenImmersion ((toChartIntersection f hL d V c).left ≫ (u).left)
  infer_instance

end FLT.Mazur.OrderedHilbertBaseOpenChart
