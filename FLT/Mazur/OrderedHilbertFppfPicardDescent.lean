/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OrderedHilbertFppfChartKernel
public import FLT.Mazur.RelativePicardFppfSingletonDescent

/-!
# The effective chart retains the original Picard section

The original section on the entire constructed source descends along the
actual fppf chart projection. Its unique descent is the prescribed translated
Hilbert section, so the scheme quotient retains its original Picard meaning.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.OrderedHilbertBaseOpenChart
open HilbertChart CartierAbel SchemePicard FCurve
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R] {X : Scheme}
  (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  (d : ℕ) {V W : Over (Spec (.of R))} (b : W ⟶ V)
  [IsOpenImmersion V.hom] [Flat b.left] [LocallyOfFinitePresentation b.left]
  [Surjective b.left] (c : (relativeFppfSheaf f).obj.obj (op V))
local notation "cW" => CategoryTheory.Functor.map
  (ObjectProperty.FullSubcategory.obj (relativeFppfSheaf f)) (Quiver.Hom.op b) c
local notation "s" => OrderedHilbertIdentityOriginalSection.sourceSection f hL

omit [IsOpenImmersion V.hom] [Flat b.left] [LocallyOfFinitePresentation b.left]
  [Surjective b.left] in
/-- The actual parameter change pulls back the prescribed original translating section. -/
theorem fppfChartChange_section :
    (relativeFppfSheaf f).obj.map (baseMarkedChartChange f b d).op
      (variableChartSection f hL d V c) = variableChartSection f hL d W cW := by
  rw [variableChartSection_map]
  simpa only [Category.id_comp, baseMarkedIndexChange, variableChartSection] using
    baseMarkedChartChange_class f hL b (d, c) (𝟙 _)

omit [IsOpenImmersion V.hom] [Flat b.left] [LocallyOfFinitePresentation b.left]
  [Surjective b.left] in
/-- The composite geometric projection preserves the original Picard class on the full source. -/
theorem fppfChartProjection_section :
    (relativeFppfSheaf f).obj.map (fppfChartProjection f hL d b c).op
      (variableChartSection f hL d V c) =
        (relativeFppfSheaf f).obj.map (inclusion f hL d W cW).op s := by
  simp only [fppfChartProjection, op_comp, Functor.map_comp, ConcreteCategory.comp_apply,
    fppfChartChange_section]
  exact (original_class f hL d W cW).symm

omit [IsOpenImmersion V.hom] in
/-- The effective quotient section is uniquely fixed by its original full-source section. -/
theorem fppfChartProjection_section_unique
    (t : (relativeFppfSheaf f).obj.obj (op (variableHilbertTest f d V)))
    (ht : (relativeFppfSheaf f).obj.map (fppfChartProjection f hL d b c).op t =
      (relativeFppfSheaf f).obj.map (inclusion f hL d W cW).op s) :
    t = variableChartSection f hL d V c :=
  relativePicardFppf_singleton_injective f (fppfChartProjection f hL d b c)
    (ht.trans (fppfChartProjection_section f hL d b c).symm)

omit [IsOpenImmersion V.hom] in
/-- The actual original section has this unique descent through the full effective quotient. -/
theorem fppfChartProjection_section_existsUnique :
    ∃! t : (relativeFppfSheaf f).obj.obj (op (variableHilbertTest f d V)),
      (relativeFppfSheaf f).obj.map (fppfChartProjection f hL d b c).op t =
        (relativeFppfSheaf f).obj.map (inclusion f hL d W cW).op s :=
  ⟨variableChartSection f hL d V c, fppfChartProjection_section f hL d b c,
    fppfChartProjection_section_unique f hL d b c⟩

end FLT.Mazur.OrderedHilbertBaseOpenChart
