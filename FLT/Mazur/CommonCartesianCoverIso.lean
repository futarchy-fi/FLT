/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.FlatDescent

/-!
# Comparing two models recovered by the same Cartesian cover

A morphism between two models is an isomorphism if their recoveries through
the same faithfully flat quasi-compact base cover are literally identical.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.CommonCartesianCoverIso

universe u
variable {A X Y B S : Scheme.{u}} {a : A ⟶ X} {b : A ⟶ Y} {t : A ⟶ B}
  {x : X ⟶ S} {y : Y ⟶ S} {k : B ⟶ S}
  (H₁ : IsPullback a t x k) (H₂ : IsPullback b t y k)
  [Surjective k] [Flat k] [QuasiCompact k]

include H₁ H₂ in
/-- A map inducing the identical common Cartesian recovery is an isomorphism. -/
theorem isIso (f : X ⟶ Y) (hf : a ≫ f = b) (hb : f ≫ y = x) : IsIso f := by
  have H : IsPullback (𝟙 A) a b f := by
    apply IsPullback.of_right (h₁₂ := t) (h₂₂ := y) (v₁₃ := k) _ _ H₂.flip
    · simpa only [Category.id_comp, hb] using H₁.flip
    · simpa only [Category.id_comp] using hf.symm
  have hs : Surjective b := MorphismProperty.of_isPullback H₂.flip inferInstance
  have hfl : Flat b := MorphismProperty.of_isPullback H₂.flip inferInstance
  have hqc : QuasiCompact b := MorphismProperty.of_isPullback H₂.flip inferInstance
  exact MorphismProperty.of_isPullback_of_descendsAlong
    (P := MorphismProperty.isomorphisms Scheme)
    (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) H ⟨⟨hs, hfl⟩, hqc⟩ (by
      change IsIso (𝟙 A)
      infer_instance)

end FLT.Mazur.CommonCartesianCoverIso
