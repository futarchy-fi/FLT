/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AcyclicHilbertPicardTestOverlap

/-!
# Translated Hilbert Abel charts and their actual test intersections

Translation by an original base Picard section preserves the parameter scheme
and its injective map on every test. The constructed intersection with every
test is an actual open immersion with the full fiber-product universal property.
No assertion that a particular collection of translations covers Picard is made.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart
open CartierAbel SchemePicard FCurve
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] {X : Scheme} (f : X ⟶ Spec (.of R))

/-- Restrict an original base Picard-sheaf section to an arbitrary relative test. -/
def basePicardSection (c : (relativeFppfSheaf f).obj.obj (op (Over.mk (𝟙 (Spec (.of R))))))
    (U : Over (Spec (.of R))) : (relativeFppfSheaf f).obj.obj (op U) :=
  (relativeFppfSheaf f).obj.map (Over.homMk U.hom).op c

/-- Restrictions of the original base section commute with every test morphism. -/
theorem basePicardSection_natural
    (c : (relativeFppfSheaf f).obj.obj (op (Over.mk (𝟙 (Spec (.of R))))))
    {U V : Over (Spec (.of R))} (b : V ⟶ U) :
    (relativeFppfSheaf f).obj.map b.op (basePicardSection f c U) =
      basePicardSection f c V := by
  have he : b ≫ (Over.homMk U.hom : U ⟶ Over.mk (𝟙 (Spec (.of R)))) =
      Over.homMk V.hom := Over.OverMorphism.ext (Over.w b)
  unfold basePicardSection
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp, he]

variable [Algebra.FiniteType ℤ R] [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] (d : ℕ) {L : X.Modules} (hL : AmpleLineBundle L)
  (c : (relativeFppfSheaf f).obj.obj (op (Over.mk (𝟙 (Spec (.of R))))))

/-- The actual Hilbert parameter chart translated by the inverse of a fixed base class. -/
def translatedHilbertPicardPoint (U : Over (Spec (.of R)))
    (k : U ⟶ acyclicHilbertTest f d) : (relativeFppfSheaf f).obj.obj (op U) :=
  (show (relativeFppfSheaf f).obj.obj (op U) from
    acyclicHilbertPicardPoint f d hL U k) / basePicardSection f c U

/-- The translated class remains natural for every original test map. -/
theorem translatedHilbertPicardPoint_natural {U V : Over (Spec (.of R))}
    (b : V ⟶ U) (k : U ⟶ acyclicHilbertTest f d) :
    translatedHilbertPicardPoint f d hL c V (b ≫ k) =
      (relativeFppfSheaf f).obj.map b.op (translatedHilbertPicardPoint f d hL c U k) := by
  unfold translatedHilbertPicardPoint
  rw [acyclicHilbertPicardPoint_natural, map_div, basePicardSection_natural]

/-- Translated charts still distinguish all maps to the actual parameter scheme. -/
theorem translatedHilbertPicardPoint_injective (U : Over (Spec (.of R))) :
    Function.Injective (translatedHilbertPicardPoint f d hL c U) := by
  intro k l h
  apply acyclicHilbertPicardPoint_injective f d hL U
  exact div_left_inj.mp h

variable (T : Over (Spec (.of R))) (s : (relativeFppfSheaf f).obj.obj (op T))

/-- The exact class equation before translation, with no chosen line representative. -/
theorem translatedHilbertPicardPoint_eq_iff {U : Over (Spec (.of R))}
    (b : U ⟶ T) (k : U ⟶ acyclicHilbertTest f d) :
    translatedHilbertPicardPoint f d hL c U k = (relativeFppfSheaf f).obj.map b.op s ↔
      acyclicHilbertPicardPoint f d hL U k =
        (relativeFppfSheaf f).obj.map b.op (s * basePicardSection f c T) := by
  rw [map_mul, basePicardSection_natural]
  exact div_eq_iff_eq_mul

/-- An actual open scheme representing the intersection with a translated chart. -/
def translatedHilbertOverlapTest : Over (Spec (.of R)) :=
  unpointedAcyclicDegreeTest f T (s * basePicardSection f c T) d

/-- The original open immersion from the intersection into the given test. -/
def translatedHilbertOverlapArrow : translatedHilbertOverlapTest f d c T s ⟶ T :=
  unpointedAcyclicDegreeArrow f T (s * basePicardSection f c T) d

instance translatedHilbertOverlapArrow_isOpenImmersion :
    IsOpenImmersion (translatedHilbertOverlapArrow f d c T s).left :=
  unpointedAcyclicDegreeArrow_isOpenImmersion _ _ _ _

/-- The actual intersection's map to the unchanged Hilbert parameter scheme. -/
def translatedHilbertOverlapToParameter :
    translatedHilbertOverlapTest f d c T s ⟶ acyclicHilbertTest f d :=
  acyclicHilbertPicardOverlapToParameter f d hL T (s * basePicardSection f c T)

/-- The original section and the translated parameter class agree on the intersection. -/
theorem translatedHilbertOverlap_class :
    translatedHilbertPicardPoint f d hL c _ (translatedHilbertOverlapToParameter f d hL c T s) =
      (relativeFppfSheaf f).obj.map (translatedHilbertOverlapArrow f d c T s).op s := by
  apply (translatedHilbertPicardPoint_eq_iff f d hL c T s _ _).mpr
  exact acyclicHilbertPicardOverlap_class f d hL T (s * basePicardSection f c T)

/-- Every translated Hilbert Abel chart has an actual open intersection with every test. -/
theorem translatedHilbertOverlap_lift {U : Over (Spec (.of R))}
    (b : U ⟶ T) (k : U ⟶ acyclicHilbertTest f d)
    (hk : translatedHilbertPicardPoint f d hL c U k = (relativeFppfSheaf f).obj.map b.op s) :
    ∃! l : U ⟶ translatedHilbertOverlapTest f d c T s,
      l ≫ translatedHilbertOverlapArrow f d c T s = b ∧
        l ≫ translatedHilbertOverlapToParameter f d hL c T s = k :=
  acyclicHilbertPicardOverlap_lift f d hL T (s * basePicardSection f c T) b k
    ((translatedHilbertPicardPoint_eq_iff f d hL c T s b k).mp hk)

end FLT.Mazur.HilbertChart
