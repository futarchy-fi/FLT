/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineHilbertFullFiberInterior

/-!
# Full envelopes for subterminal translations

When the translation embeds in the coefficient base, reflexivity fills the
entire independent envelope. This tests actual scheme fibers, with no pointwise
residue-field uniqueness assumption.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart.AffineRestriction
open CartierAbel SchemePicard FCurve SchemeOpenEnvelope
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R] {X : Scheme}
  (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  (d : ℕ) (V : Over (Spec (.of R))) [Mono V.hom]
  (c : (relativeFppfSheaf f).obj.obj (op V))
  {A : Over (Spec (.of R))} (k : A ⟶ variableHilbertTest f d V)
  [IsOpenImmersion k.left]
local notation "e" => equivalence f hL d V c k
local notation "j" => toEnvelope f hL d V c k

omit [IsOpenImmersion k.left] in
/-- Reflexivity is a right inverse on the entire independent envelope. -/
theorem subterminalEnvelope_section :
    (prod.fst : prod A V ⟶ A) ≫ (e).r ≫ j = 𝟙 _ := by
  apply prod.hom_ext
  · simp only [Category.assoc, toEnvelope_test, (e).reflexivity₂, Category.comp_id,
      Category.id_comp]
  · apply Over.OverMorphism.ext
    apply (cancel_mono V.hom).mp
    exact (Over.w _).trans (Over.w _).symm

/-- Subterminal translations have an effective full original relation on every open chart. -/
instance subterminal_toEnvelope_isIso : IsIso (j).left := by
  let _ : IsSplitEpi (j).left := IsSplitEpi.mk'
    ⟨((prod.fst : prod A V ⟶ A) ≫ (e).r).left,
      congrArg Over.Hom.left (subterminalEnvelope_section f hL d V c k)⟩
  exact isIso_of_mono_of_isSplitEpi (j).left

/-- No initial full-fiber point is required for a subterminal translation. -/
theorem subterminal_fullEnvelopeLocus : fullEnvelopeLocus f hL d V c k = Set.univ := by
  apply Set.eq_univ_of_forall
  intro x
  apply (mem_fullFiberLocus _ _ x).mpr
  intro y _
  exact (j).left.surjective y

/-- Every point lies in the full-fiber interior as well. -/
theorem subterminal_fullEnvelopeInterior : fullEnvelopeInterior f hL d V c k = ⊤ := by
  apply SetLike.coe_injective
  rw [fullEnvelopeInterior_coe, subterminal_fullEnvelopeLocus, interior_univ]
  rfl

end FLT.Mazur.HilbertChart.AffineRestriction
