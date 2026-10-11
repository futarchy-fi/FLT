/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.NonspecialDivisorTranslationCover
public import FLT.Mazur.HilbertDivisorDegreePresentation
public import FLT.Mazur.VariableTranslatedHilbertChart

/-!
# Local Hilbert translations of every original Picard section

Refining the constructed divisor-and-line cover by the actual degree opens
gives a single small fppf cover. Every member maps to the genuine Hilbert
parameter scheme, and translation by an actual line recovers the supplied
Picard section. No global base translation is assumed sufficient.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart
open CartierAbel FCurve SchemePicard
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R]
  {X : Scheme} (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {B : X.Modules} (hB : AmpleLineBundle B)

include hB in
/-- Actual Hilbert parameters and line translations locally present every original section. -/
theorem exists_local_hilbert_translation_cover (T : Over (Spec (.of R)))
    (s : (relativeFppfSheaf f).obj.obj (op T)) :
    ∃ C : Scheme.Cover.{0} Scheme.fppfPrecoverage T.left, ∀ i,
      ∃ (d : ℕ) (k : relativeCoverMember T C i ⟶ acyclicHilbertTest f d)
        (M : LineBundle (pullback f (relativeCoverMember T C i).hom)),
        (show (relativeFppfSheaf f).obj.obj (op (relativeCoverMember T C i)) from
          acyclicHilbertPicardPoint f d hB _ k) /
          relativeFppfClass f _ (relativeClass _ (mk M.val M.property)) =
            (relativeFppfSheaf f).obj.map (relativeCoverArrow T C i).op s := by
  obtain ⟨C, hC⟩ := exists_nonspecial_divisor_translation_cover f hB T s
  choose D L M _ _ hM using hC
  let E i := (divisorDegreePresentationCover f (relativeCoverMember T C i) (D i)).weaken
    Scheme.zariskiPrecoverage_le_fppfPrecoverage
  let F := C.bind E
  refine ⟨F, fun i ↦ ?_⟩
  let V := relativeCoverMember T C i.1
  let W := relativeCoverMember T F i
  let a : W ⟶ V := Over.homMk ((E i.1).f i.2) (by
    simp only [relativeCoverMember]; rfl)
  let b : W ⟶ acyclicDivisorDegreeTest f V (D i.1) i.2 := Over.homMk (𝟙 _) (by
    simp only [acyclicDivisorDegreeTest, Category.id_comp]; rfl)
  let N := (Scheme.Modules.pullback (relativeTotalMap f a)).obj (M i.1).val
  have hN := (M i.1).property.pullback (relativeTotalMap f a)
  let k := b ≫ divisorDegreeParameter f hB V (D i.1) i.2
  refine ⟨i.2, k, ⟨N, hN⟩, ?_⟩
  have hab : b ≫ acyclicDivisorDegreeArrow f V (D i.1) i.2 = a := by
    apply Over.OverMorphism.ext
    exact Category.id_comp _
  have hp : acyclicHilbertPicardPoint f i.2 hB W k =
      (relativeFppfSheaf f).obj.map a.op
        (relativeFppfClass f V (abel _ (D i.1).val)) := by
    rw [acyclicHilbertPicardPoint_natural, divisorDegreeParameter_class]
    rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp, hab]
  rw [hp]
  change _ / relativeFppfClass f W
    (relativeBaseMap f a (relativeClass _ (mk (M i.1).val (M i.1).property))) = _
  rw [← relativeFppfClass_naturality, ← map_div, hM]
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp]
  congr 2

include hB in
/-- Every section is locally in actual variable-base charts with original line translations. -/
theorem exists_local_variable_hilbert_cover (T : Over (Spec (.of R)))
    (s : (relativeFppfSheaf f).obj.obj (op T)) :
    ∃ C : Scheme.Cover.{0} Scheme.fppfPrecoverage T.left, ∀ i,
      ∃ (d : ℕ) (M : LineBundle (pullback f (relativeCoverMember T C i).hom))
        (k : relativeCoverMember T C i ⟶ variableHilbertTest f d (relativeCoverMember T C i)),
        k ≫ variableHilbertBase f d (relativeCoverMember T C i) = 𝟙 _ ∧
        variableHilbertPoint f d hB (relativeCoverMember T C i)
          (relativeFppfClass f _ (relativeClass _ (mk M.val M.property))) _ k =
            (relativeFppfSheaf f).obj.map (relativeCoverArrow T C i).op s := by
  obtain ⟨C, hC⟩ := exists_local_hilbert_translation_cover f hB T s
  refine ⟨C, fun i ↦ ?_⟩
  obtain ⟨d, k, M, hk⟩ := hC i
  refine ⟨d, M, variableHilbertLift f d _ (𝟙 _) k, prod.lift_fst _ _, ?_⟩
  rw [variableHilbertPoint_lift]
  rw [op_id]
  change _ / ((relativeFppfSheaf f).obj.map (𝟙 _)).hom _ = _
  rw [(relativeFppfSheaf f).obj.map_id]
  exact hk

end FLT.Mazur.HilbertChart
