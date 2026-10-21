/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.AlgebraicGeometry.Gluing

/-!
# Full comparison lifts on unions of open neighborhoods

For a monomorphic comparison, local lifts agree on the actual scheme overlaps.
They glue uniquely, with no separate compatibility assumption and without
passing to reduced schemes. Arbitrary unions of lift neighborhoods are allowed.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.MonoComparisonOpenGluing
universe u v
variable {C T B : Scheme.{u}} (c : C ⟶ T) [Mono c] (t : B ⟶ T)

/-- Actual local lifts on an open cover construct a unique full comparison arrow. -/
theorem existsUnique_of_cover (U : B.OpenCover)
    (h : ∀ i, ∃ d : U.X i ⟶ C, d ≫ c = U.f i ≫ t) :
    ∃! d : B ⟶ C, d ≫ c = t := by
  choose d hd using h
  have hc (i j) : pullback.fst (U.f i) (U.f j) ≫ d i =
      pullback.snd (U.f i) (U.f j) ≫ d j := by
    apply (cancel_mono c).mp
    simp only [Category.assoc, hd, pullback.condition_assoc]
  refine ⟨U.glueMorphisms d hc, ?_, ?_⟩
  · apply U.hom_ext
    intro i
    rw [← Category.assoc, U.ι_glueMorphisms, hd]
  · intro d' hd'
    apply (cancel_mono c).mp
    rw [hd']
    apply U.hom_ext
    intro i
    rw [← Category.assoc, U.ι_glueMorphisms, hd]

/-- All supplied open lift neighborhoods glue over their entire union. -/
theorem existsUnique_on_union {I : Type v} (U : I → B.Opens)
    (h : ∀ i, ∃ d : (U i).toScheme ⟶ C, d ≫ c = (U i).ι ≫ t) :
    ∃! d : (⨆ i, U i).toScheme ⟶ C, d ≫ c = (⨆ i, U i).ι ≫ t := by
  apply existsUnique_of_cover c _ (Scheme.Opens.iSupOpenCover U)
  intro i
  obtain ⟨d, hd⟩ := h i
  refine ⟨d, ?_⟩
  simpa only [Scheme.Opens.iSupOpenCover, ← Category.assoc, Scheme.homOfLE_ι] using hd

end FLT.Mazur.MonoComparisonOpenGluing
