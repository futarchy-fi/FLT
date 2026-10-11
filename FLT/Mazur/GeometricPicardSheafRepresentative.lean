/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GeometricFppfCoverSection
public import FLT.Mazur.RelativeFppfComparisonCover

/-!
# Actual line representatives of geometric Picard-sheaf sections

A split member of the comparison cover pulls a local line representative
back to the original geometric test. No section of the original family is
assumed, and the original quotient and sheafification are unchanged.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
universe u
namespace FLT.Mazur.SchemePicard
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {X S : Scheme.{u}} (f : X ⟶ S)
  {k : Type u} [Field k] [IsAlgClosed k] (g : Spec (.of k) ⟶ S)

/-- Every original sheaf section on a geometric test is represented by an actual line. -/
theorem exists_geometric_picardSheaf_line
    (s : (relativeFppfSheaf f).obj.obj (op (Over.mk g))) :
    ∃ L : LineBundle (Limits.pullback f g),
      relativeFppfClass f (Over.mk g) (relativeClass _ (mk L.val L.property)) = s := by
  obtain ⟨C, hC⟩ := relativeFppfClass_exists_cover f (Over.mk g) s
  obtain ⟨i, b, hb⟩ := SchemeFppfFamily.exists_relative_cover_section g C
  obtain ⟨c, hc⟩ := hC i
  have hline : ∃ L : LineBundle (Limits.pullback f
      (relativeCoverMember (Over.mk g) C i).hom), relativeClass _ (mk L.val L.property) = c := by
    obtain ⟨v, rfl⟩ := relativeClass_surjective _ c
    induction v using inductionOn with
    | h L hL => exact ⟨⟨L, hL⟩, rfl⟩
  obtain ⟨L, hL⟩ := hline
  let M := (Scheme.Modules.pullback (relativeTotalMap f b)).obj L.val
  have hM := L.property.pullback (relativeTotalMap f b)
  refine ⟨⟨M, hM⟩, ?_⟩
  change relativeFppfClass f _ (relativeBaseMap f b (relativeClass _
    (mk L.val L.property))) = s
  rw [hL, ← relativeFppfClass_naturality, hc]
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp, hb, op_id]
  exact ConcreteCategory.congr_hom ((relativeFppfSheaf f).obj.map_id _) s

end FLT.Mazur.SchemePicard
