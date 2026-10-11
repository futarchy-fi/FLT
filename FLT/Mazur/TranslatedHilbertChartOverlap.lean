/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.TranslatedHilbertPicardChart

/-!
# Actual open overlaps of translated Hilbert charts

Any two translated parameter charts have a scheme-theoretic intersection
with its full test-map universal property. Swapping the two charts gives
an actual isomorphism, and both overlap projections are open immersions.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart
open CartierAbel SchemePicard FCurve
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] {X : Scheme} (f : X ⟶ Spec (.of R))

/-- A degree and an original base Picard section specify a translated Hilbert chart. -/
abbrev TranslatedHilbertIndex :=
  ℕ × (relativeFppfSheaf f).obj.obj (op (Over.mk (𝟙 (Spec (.of R)))))

variable [Algebra.FiniteType ℤ R] [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  (i j : TranslatedHilbertIndex f)

/-- The original Picard section on the actual translated chart. -/
def translatedHilbertChartSection :
    (relativeFppfSheaf f).obj.obj (op (acyclicHilbertTest f i.1)) :=
  translatedHilbertPicardPoint f i.1 hL i.2 _ (𝟙 _)

/-- Restricting the chart's section is its actual translated parameter class. -/
theorem translatedHilbertChartSection_map {U : Over (Spec (.of R))}
    (b : U ⟶ acyclicHilbertTest f i.1) :
    (relativeFppfSheaf f).obj.map b.op (translatedHilbertChartSection f hL i) =
      translatedHilbertPicardPoint f i.1 hL i.2 U b := by
  simpa only [Category.comp_id, translatedHilbertChartSection] using
    (translatedHilbertPicardPoint_natural f i.1 hL i.2 b (𝟙 _)).symm

/-- The actual open intersection scheme for the two translated parameter charts. -/
def translatedHilbertChartOverlap : Over (Spec (.of R)) :=
  translatedHilbertOverlapTest f j.1 j.2 _ (translatedHilbertChartSection f hL i)

/-- The first overlap projection. -/
def translatedHilbertChartOverlapLeft :
    translatedHilbertChartOverlap f hL i j ⟶ acyclicHilbertTest f i.1 :=
  translatedHilbertOverlapArrow f j.1 j.2 _ (translatedHilbertChartSection f hL i)

/-- The second overlap projection. -/
def translatedHilbertChartOverlapRight :
    translatedHilbertChartOverlap f hL i j ⟶ acyclicHilbertTest f j.1 :=
  translatedHilbertOverlapToParameter f j.1 hL j.2 _ (translatedHilbertChartSection f hL i)

instance translatedHilbertChartOverlapLeft_isOpenImmersion :
    IsOpenImmersion (translatedHilbertChartOverlapLeft f hL i j).left :=
  translatedHilbertOverlapArrow_isOpenImmersion _ _ _ _ _

instance translatedHilbertChartOverlapLeft_mono :
    Mono (translatedHilbertChartOverlapLeft f hL i j) := Over.mono_of_mono_left _

/-- Both projections give exactly the same original Picard-sheaf section. -/
theorem translatedHilbertChartOverlap_class :
    translatedHilbertPicardPoint f i.1 hL i.2 _ (translatedHilbertChartOverlapLeft f hL i j) =
      translatedHilbertPicardPoint f j.1 hL j.2 _
        (translatedHilbertChartOverlapRight f hL i j) := by
  rw [← translatedHilbertChartSection_map]
  exact (translatedHilbertOverlap_class f j.1 hL j.2 _
    (translatedHilbertChartSection f hL i)).symm

/-- Compatible parameter maps factor uniquely through the actual overlap. -/
theorem translatedHilbertChartOverlap_lift {U : Over (Spec (.of R))}
    (a : U ⟶ acyclicHilbertTest f i.1) (b : U ⟶ acyclicHilbertTest f j.1)
    (h : translatedHilbertPicardPoint f i.1 hL i.2 U a =
      translatedHilbertPicardPoint f j.1 hL j.2 U b) :
    ∃! k : U ⟶ translatedHilbertChartOverlap f hL i j,
      k ≫ translatedHilbertChartOverlapLeft f hL i j = a ∧
        k ≫ translatedHilbertChartOverlapRight f hL i j = b := by
  apply translatedHilbertOverlap_lift f j.1 hL j.2 _
    (translatedHilbertChartSection f hL i) a b
  rw [translatedHilbertChartSection_map]
  exact h.symm

/-- Exchange the two actual charts using the proved intersection universal property. -/
def translatedHilbertChartOverlapSwap :
    translatedHilbertChartOverlap f hL i j ⟶ translatedHilbertChartOverlap f hL j i :=
  (translatedHilbertChartOverlap_lift f hL j i
    (translatedHilbertChartOverlapRight f hL i j) (translatedHilbertChartOverlapLeft f hL i j)
    (translatedHilbertChartOverlap_class f hL i j).symm).choose

@[reassoc]
lemma translatedHilbertChartOverlapSwap_left :
    translatedHilbertChartOverlapSwap f hL i j ≫ translatedHilbertChartOverlapLeft f hL j i =
      translatedHilbertChartOverlapRight f hL i j :=
  (translatedHilbertChartOverlap_lift f hL j i _ _
    (translatedHilbertChartOverlap_class f hL i j).symm).choose_spec.1.1

@[reassoc]
lemma translatedHilbertChartOverlapSwap_right :
    translatedHilbertChartOverlapSwap f hL i j ≫ translatedHilbertChartOverlapRight f hL j i =
      translatedHilbertChartOverlapLeft f hL i j :=
  (translatedHilbertChartOverlap_lift f hL j i _ _
    (translatedHilbertChartOverlap_class f hL i j).symm).choose_spec.1.2

/-- Exchanging the charts is an actual isomorphism of their intersection schemes. -/
def translatedHilbertChartOverlapSymmetry :
    translatedHilbertChartOverlap f hL i j ≅ translatedHilbertChartOverlap f hL j i where
  hom := translatedHilbertChartOverlapSwap f hL i j
  inv := translatedHilbertChartOverlapSwap f hL j i
  hom_inv_id := by
    rw [← cancel_mono (translatedHilbertChartOverlapLeft f hL i j), Category.assoc,
      translatedHilbertChartOverlapSwap_left, translatedHilbertChartOverlapSwap_right,
      Category.id_comp]
  inv_hom_id := by
    rw [← cancel_mono (translatedHilbertChartOverlapLeft f hL j i), Category.assoc,
      translatedHilbertChartOverlapSwap_left, translatedHilbertChartOverlapSwap_right,
      Category.id_comp]

/-- The second projection is open as well, via the constructed symmetry isomorphism. -/
instance translatedHilbertChartOverlapRight_isOpenImmersion :
    IsOpenImmersion (translatedHilbertChartOverlapRight f hL i j).left := by
  have he := congrArg Over.Hom.left (translatedHilbertChartOverlapSwap_left f hL i j)
  rw [← he]
  change IsOpenImmersion ((translatedHilbertChartOverlapSymmetry f hL i j).hom.left ≫
    (translatedHilbertChartOverlapLeft f hL j i).left)
  infer_instance

end FLT.Mazur.HilbertChart
