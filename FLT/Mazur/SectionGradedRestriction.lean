/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SectionGradedAlgebra

/-!
# Detecting homogeneous sections on an open cover

Restriction of the section ring preserves scalars through the actual
structure-sheaf map. A homogeneous element vanishes if it vanishes on a cover.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u v
namespace FLT.Mazur.SectionGradedRestriction
open FCurve ModuleLineBundleTensorPullback SectionGradedSum SectionGradedMultiplication
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {X : Scheme.{u}} (L : X.Modules)

/-- Inclusion of a section into the full graded ring reflects zero. -/
lemma of_eq_zero_iff (U : X.Opens) (n : ℕ) (s : Piece L U n) :
    of L U n s = 0 ↔ s = 0 := by
  constructor
  · intro h
    apply DirectSum.of_injective n
    exact h.trans (map_zero (of L U n)).symm
  · rintro rfl
    exact map_zero _

/-- Restriction of the full ring respects the actual restriction of scalar functions. -/
lemma restrict_smul {U V : X.Opens} (i : U ⟶ V) (a : Γ(X, V)) (z : SectionGradedSum.Sections L V) :
    restrictRingHom L U i (a • z) = X.presheaf.map i.op a • restrictRingHom L U i z := by
  induction z using DirectSum.induction_on with
  | zero => simp
  | of n s =>
    change restrict L i (a • of L V n s) = _
    rw [← _root_.map_smul, restrict_of]
    erw [(tensorPower L n).val.map_smul]
    change of L U n (X.presheaf.map i.op a •
      (tensorPower L n).presheaf.map i.op s) = _
    rw [_root_.map_smul]
    exact congrArg (fun z ↦ X.presheaf.map i.op a • z) (restrict_of L i n s).symm
  | add a b ha hb => simp only [smul_add, map_add, ha, hb]

/-- Vanishing on an open cover detects every homogeneous global ring element. -/
lemma eq_zero_of_cover {ι : Type v} (U : ι → X.Opens) (hU : ⨆ i, U i = ⊤)
    {n : ℕ} {z : SectionGradedSum.Sections L ⊤} (hz : z ∈ grade L ⊤ n)
    (h : ∀ i, restrictRingHom L (U i) (homOfLE le_top) z = 0) : z = 0 := by
  obtain ⟨t, rfl⟩ := hz
  apply (of_eq_zero_iff L ⊤ n t).mpr
  apply TopCat.Sheaf.eq_of_locally_eq'
    (⟨(tensorPower L n).presheaf, (tensorPower L n).isSheaf⟩ : TopCat.Sheaf Ab X)
    U ⊤ (fun _ ↦ homOfLE le_top) (by rw [hU])
  intro i
  rw [map_zero]
  apply (of_eq_zero_iff L (U i) n _).mp
  exact (restrict_of L _ n t).symm.trans (h i)

end FLT.Mazur.SectionGradedRestriction
