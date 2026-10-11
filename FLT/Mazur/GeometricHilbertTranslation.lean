/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GeometricFppfCoverSection
public import FLT.Mazur.LocalHilbertTranslationCover

/-!
# Hilbert translations on the original geometric test

Splitting the constructed covering family gives an actual Hilbert point and
an actual translation line on the geometric test itself. This applies to
arbitrary original Picard-sheaf sections, without a supplied representative.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart
open CartierAbel FCurve SchemePicard
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] acyclicHilbertPicardPoint
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R]
  {X : Scheme} (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {B : X.Modules} (hB : AmpleLineBundle B)
  {k : Type} [Field k] [IsAlgClosed k] (g : Spec (.of k) ⟶ Spec (.of R))

include hB in
/-- Every geometric original sheaf section has a Hilbert point and a line translation. -/
theorem exists_geometric_hilbert_translation
    (s : (relativeFppfSheaf f).obj.obj (op (Over.mk g))) :
    ∃ (d : ℕ) (a : Over.mk g ⟶ acyclicHilbertTest f d) (M : LineBundle (pullback f g)),
      (show (relativeFppfSheaf f).obj.obj (op (Over.mk g)) from
        acyclicHilbertPicardPoint f d hB _ a) /
          relativeFppfClass f (Over.mk g) (relativeClass _ (mk M.val M.property)) = s := by
  obtain ⟨C, hC⟩ := exists_local_hilbert_translation_cover f hB (Over.mk g) s
  obtain ⟨i, b, hb⟩ := SchemeFppfFamily.exists_relative_cover_section g C
  obtain ⟨d, a, M, ha⟩ := hC i
  let N := (Scheme.Modules.pullback (relativeTotalMap f b)).obj M.val
  have hN := M.property.pullback (relativeTotalMap f b)
  refine ⟨d, b ≫ a, ⟨N, hN⟩, ?_⟩
  rw [acyclicHilbertPicardPoint_natural]
  change _ / relativeFppfClass f _ (relativeBaseMap f b
    (relativeClass _ (mk M.val M.property))) = s
  rw [← relativeFppfClass_naturality, ← map_div, ha]
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp, hb, op_id]
  exact ConcreteCategory.congr_hom ((relativeFppfSheaf f).obj.map_id _) s

end FLT.Mazur.HilbertChart
