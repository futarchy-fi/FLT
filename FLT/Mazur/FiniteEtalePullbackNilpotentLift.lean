/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineEtaleNilpotentLift
public import Mathlib.AlgebraicGeometry.Morphisms.Finite

/-!
# Extend original arrows using the full finite etale coefficient source

The ambient source need not be affine. Its entire finite coefficient pullback
is affine over the specified affine test, so affine formal etaleness applies
there. The constructed original arrow preserves its first endpoint and its
restriction to the nilpotent closed test, uniquely.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.FiniteEtalePullbackNilpotentLift
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {Z B D A : Scheme.{0}} [IsAffine B]
  (i : Z ⟶ B) [IsClosedImmersion i] (hi : IsNilpotent i.ker)
  (p : D ⟶ A) [Etale p] (a : Z ⟶ D) (b : B ⟶ A)
  [IsFinite (pullback.snd p b)] (h : a ≫ p = i ≫ b)

include hi h in
/-- The entire finite endpoint source constructs a unique original arrow over the thickening. -/
theorem existsUnique_lift : ∃! d : B ⟶ D, i ≫ d = a ∧ d ≫ p = b := by
  let _ : IsAffine Z := isAffine_of_isAffineHom i
  let _ : IsAffine (pullback p b) := isAffine_of_isAffineHom (pullback.snd p b)
  let a' : Z ⟶ pullback p b := pullback.lift a i h
  have ha' : i ≫ 𝟙 B = a' ≫ pullback.snd p b := by
    rw [Category.comp_id, pullback.lift_snd]
  obtain ⟨s, hs, hu⟩ := AffineEtaleNilpotentLift.existsUnique_lift i hi
    (pullback.snd p b) a' (𝟙 B) ha'
  refine ⟨s ≫ pullback.fst p b, ⟨?_, ?_⟩, ?_⟩
  · rw [← Category.assoc, hs.1, pullback.lift_fst]
  · rw [Category.assoc, pullback.condition, ← Category.assoc, hs.2, Category.id_comp]
  · intro d hd
    let s' : B ⟶ pullback p b := pullback.lift d (𝟙 B)
      (hd.2.trans (Category.id_comp b).symm)
    have hs' : i ≫ s' = a' ∧ s' ≫ pullback.snd p b = 𝟙 B := by
      constructor
      · apply pullback.hom_ext
        · simp only [Category.assoc, s', a', pullback.lift_fst, hd.1]
        · simp only [Category.assoc, s', a', pullback.lift_snd, Category.comp_id]
      · exact pullback.lift_snd _ _ _
    have he : s' = s := hu s' hs'
    calc
      d = s' ≫ pullback.fst p b := (pullback.lift_fst _ _ _).symm
      _ = s ≫ pullback.fst p b := congrArg (fun v ↦ v ≫ pullback.fst p b) he

end FLT.Mazur.FiniteEtalePullbackNilpotentLift
