/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OrderedHilbertOriginalTestCover
public import FLT.Mazur.BaseOpenHilbertBaseChange

/-!
# Actual scheme-chart covers from the entire constructed presentation

Pull the entire constructed source back to a translated Hilbert chart over
an open coefficient base. Its projection is a constructed surjective etale
scheme map. Equal chart parameters detect precisely the full original relation.
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

/-- The actual full inverse image of the chart in the entire constructed source. -/
def source : Over (Spec (.of R)) :=
  OrderedHilbertOriginalTestIntersection.relation f hL Z sZ

/-- Its original source arrow retains every component. -/
def inclusion : source f hL d V c ⟶ U :=
  OrderedHilbertOriginalTestIntersection.fst f hL Z sZ

/-- The actual geometric projection to the unchanged Hilbert scheme chart. -/
def projection : source f hL d V c ⟶ Z :=
  OrderedHilbertOriginalTestIntersection.snd f hL Z sZ

instance projection_etale : Etale (projection f hL d V c).left :=
  OrderedHilbertOriginalTestIntersection.snd_etale f hL Z sZ

instance projection_surjective : Surjective (projection f hL d V c).left :=
  OrderedHilbertOriginalTestIntersection.snd_surjective f hL Z sZ

/-- Both actual arrows retain the original Picard class. -/
theorem original_class :
    (relativeFppfSheaf f).obj.map (inclusion f hL d V c).op sU =
      (relativeFppfSheaf f).obj.map (projection f hL d V c).op sZ :=
  OrderedHilbertOriginalTestIntersection.equal_class f hL Z sZ

variable [IsOpenImmersion V.hom]

/-- On arbitrary original tests, the chart projection detects precisely original class equality. -/
theorem projection_eq_iff {T : Over (Spec (.of R))}
    (a b : T ⟶ source f hL d V c) :
    a ≫ projection f hL d V c = b ≫ projection f hL d V c ↔
      (relativeFppfSheaf f).obj.map (a ≫ inclusion f hL d V c).op sU =
        (relativeFppfSheaf f).obj.map (b ≫ inclusion f hL d V c).op sU := by
  have H (k : T ⟶ source f hL d V c) :
      (relativeFppfSheaf f).obj.map (k ≫ inclusion f hL d V c).op sU =
        variableHilbertPoint f d hL V c T (k ≫ projection f hL d V c) := by
    simp only [op_comp, Functor.map_comp, ConcreteCategory.comp_apply, original_class,
      variableChartSection_map, variableHilbertPoint_natural]
  rw [H a, H b]
  exact (baseOpenHilbertPoint_injective f hL d V c T).eq_iff.symm

end FLT.Mazur.OrderedHilbertBaseOpenChart
