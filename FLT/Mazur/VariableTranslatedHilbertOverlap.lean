/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.VariableTranslatedHilbertChart

/-!
# Actual test intersections for translations over a varying base

The intersection with an original Picard section is an open subscheme of
the product of the test and the translation base. Its two projections retain
the original section, the chosen translation, and the Hilbert parameter.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart
open CartierAbel FCurve SchemePicard
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R]
  {X : Scheme} (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] (d : ℕ) {B : X.Modules} (hB : AmpleLineBundle B)
  (T : Over (Spec (.of R))) (c : (relativeFppfSheaf f).obj.obj (op T))
  (U : Over (Spec (.of R))) (s : (relativeFppfSheaf f).obj.obj (op U))

/-- The untranslated original section on the product of test and translation base. -/
def variableHilbertProductSection : (relativeFppfSheaf f).obj.obj (op (prod U T)) :=
  (relativeFppfSheaf f).obj.map (prod.fst : prod U T ⟶ U).op s *
    (relativeFppfSheaf f).obj.map (prod.snd : prod U T ⟶ T).op c

/-- The actual open intersection in the product of the two original bases. -/
def variableHilbertOverlap : Over (Spec (.of R)) :=
  unpointedAcyclicDegreeTest f (prod U T) (variableHilbertProductSection f T c U s) d

/-- The open immersion retains both base maps. -/
def variableHilbertOverlapArrow : variableHilbertOverlap f d T c U s ⟶ prod U T :=
  unpointedAcyclicDegreeArrow f (prod U T) (variableHilbertProductSection f T c U s) d

instance variableHilbertOverlapArrow_isOpenImmersion :
    IsOpenImmersion (variableHilbertOverlapArrow f d T c U s).left :=
  unpointedAcyclicDegreeArrow_isOpenImmersion _ _ _ _

instance variableHilbertOverlapArrow_mono : Mono (variableHilbertOverlapArrow f d T c U s) :=
  Over.mono_of_mono_left _

/-- The original test projection of the intersection. -/
def variableHilbertOverlapToTest : variableHilbertOverlap f d T c U s ⟶ U :=
  variableHilbertOverlapArrow f d T c U s ≫ prod.fst

/-- The intersection maps to the actual chart, with its independent translation-base map. -/
def variableHilbertOverlapToChart :
    variableHilbertOverlap f d T c U s ⟶ variableHilbertTest f d T :=
  variableHilbertLift f d T (variableHilbertOverlapArrow f d T c U s ≫ prod.snd)
    (acyclicHilbertPicardOverlapToParameter f d hB (prod U T)
      (variableHilbertProductSection f T c U s))

/-- The intersection retains exactly the supplied original Picard section. -/
theorem variableHilbertOverlap_class :
    variableHilbertPoint f d hB T c _ (variableHilbertOverlapToChart f d hB T c U s) =
      (relativeFppfSheaf f).obj.map (variableHilbertOverlapToTest f d T c U s).op s := by
  unfold variableHilbertOverlapToChart
  rw [variableHilbertPoint_lift]
  unfold variableHilbertOverlap
  rw [acyclicHilbertPicardOverlap_class]
  simp only [variableHilbertProductSection, variableHilbertOverlapToTest,
    variableHilbertOverlapArrow, op_comp, Functor.map_comp, ConcreteCategory.comp_apply]
  apply div_eq_iff_eq_mul.mpr
  exact ((relativeFppfSheaf f).obj.map
    (variableHilbertOverlapArrow f d T c U s).op).hom.map_mul _ _

/-- The two projections distinguish all maps into the actual intersection. -/
theorem variableHilbertOverlap_hom_ext {V : Over (Spec (.of R))}
    {a b : V ⟶ variableHilbertOverlap f d T c U s}
    (ht : a ≫ variableHilbertOverlapToTest f d T c U s =
      b ≫ variableHilbertOverlapToTest f d T c U s)
    (hc : a ≫ variableHilbertOverlapToChart f d hB T c U s =
      b ≫ variableHilbertOverlapToChart f d hB T c U s) : a = b := by
  apply (cancel_mono (variableHilbertOverlapArrow f d T c U s)).mp
  apply prod.hom_ext
  · exact (Category.assoc _ _ _).trans (ht.trans (Category.assoc _ _ _).symm)
  · have hb := congrArg (fun k ↦ k ≫ variableHilbertBase f d T) hc
    simpa only [variableHilbertOverlapToChart, variableHilbertLift,
      variableHilbertBase, Category.assoc, prod.lift_fst] using hb

/-- The constructed open has the full original chart-test fiber-product property. -/
theorem variableHilbertOverlap_lift {V : Over (Spec (.of R))}
    (b : V ⟶ U) (k : V ⟶ variableHilbertTest f d T)
    (hk : variableHilbertPoint f d hB T c V k = (relativeFppfSheaf f).obj.map b.op s) :
    ∃! l : V ⟶ variableHilbertOverlap f d T c U s,
      l ≫ variableHilbertOverlapToTest f d T c U s = b ∧
        l ≫ variableHilbertOverlapToChart f d hB T c U s = k := by
  let p : V ⟶ prod U T := prod.lift b (k ≫ variableHilbertBase f d T)
  have hp : acyclicHilbertPicardPoint f d hB V (k ≫ variableHilbertParameter f d T) =
      (relativeFppfSheaf f).obj.map p.op (variableHilbertProductSection f T c U s) := by
    have he := div_eq_iff_eq_mul.mp hk
    change acyclicHilbertPicardPoint f d hB V (k ≫ variableHilbertParameter f d T) =
      (relativeFppfSheaf f).obj.map b.op s *
        (relativeFppfSheaf f).obj.map (k ≫ variableHilbertBase f d T).op c at he
    rw [variableHilbertProductSection, map_mul]
    rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp,
      ← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp]
    simpa only [p, prod.lift_fst, prod.lift_snd] using he
  obtain ⟨l, hl, _⟩ := acyclicHilbertPicardOverlap_lift f d hB (prod U T)
    (variableHilbertProductSection f T c U s) p (k ≫ variableHilbertParameter f d T) hp
  have ht : l ≫ variableHilbertOverlapToTest f d T c U s = b := by
    change l ≫ variableHilbertOverlapArrow f d T c U s ≫ prod.fst = b
    rw [← Category.assoc, show l ≫ variableHilbertOverlapArrow f d T c U s = p from hl.1]
    exact prod.lift_fst _ _
  have hc : l ≫ variableHilbertOverlapToChart f d hB T c U s = k := by
    apply prod.hom_ext
    · simp only [variableHilbertOverlapToChart, variableHilbertLift, Category.assoc,
        prod.lift_fst]
      rw [← Category.assoc, show l ≫ variableHilbertOverlapArrow f d T c U s = p from hl.1]
      exact prod.lift_snd _ _
    · simpa only [variableHilbertOverlapToChart, variableHilbertLift, Category.assoc,
        prod.lift_snd, variableHilbertParameter] using hl.2
  exact ⟨l, ⟨ht, hc⟩, fun m hm ↦ variableHilbertOverlap_hom_ext f d hB T c U s
    (hm.1.trans ht.symm) (hm.2.trans hc.symm)⟩

end FLT.Mazur.HilbertChart
