/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FinitePresentationSurjectiveScalars

/-!
# Passing ideal presentations through an ambient quotient

A finitely presented ideal containing the finitely generated kernel of a
surjective ambient map has finitely presented image. This converts polynomial
ideal presentations into presentations in finitely presented ambient algebras.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.FCurve
variable {A B : Type*} [CommRing A] [CommRing B]

/-- Quotienting the ambient by finitely many relations preserves ideal finite presentation. -/
theorem ideal_finitePresentation_map_surjective (f : A →+* B)
    (hf : Function.Surjective f) (I : Ideal A) [Module.FinitePresentation A I]
    (hker : (RingHom.ker f).FG) (hI : RingHom.ker f ≤ I) :
    Module.FinitePresentation B (I.map f) := by
  let _ : Algebra A B := f.toAlgebra
  let g := Algebra.idealMap B I
  have hg : Function.Surjective g := by
    intro y
    obtain ⟨x, hx, hxy⟩ := (Ideal.mem_map_iff_of_surjective f hf).mp y.property
    exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩
  have hk : (LinearMap.ker g).map I.subtype = RingHom.ker f := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact congrArg Subtype.val hy
    · intro hx
      exact ⟨⟨x, hI hx⟩, Subtype.ext hx, rfl⟩
  have hfg : (LinearMap.ker g).FG :=
    (Submodule.fg_map_iff I.subtype I.subtype_injective).mp (hk.symm ▸ hker)
  let _ : Module.FinitePresentation A (I.map f) :=
    Module.finitePresentation_of_surjective g hg hfg
  exact finitePresentation_of_surjective_scalars hf

end FLT.Mazur.FCurve
