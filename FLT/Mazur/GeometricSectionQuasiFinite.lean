/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.BaseChangeSectionEquiv
public import FLT.Mazur.FiniteGeometricSections
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.AlgebraicGeometry.ZariskisMainTheorem

/-!
# Quasi-finiteness from finite geometric point sets

Algebraically closed geometric tests suffice to control every residue fiber.
The proof descends finite underlying spaces along the surjection from the
algebraic-closure base change. Properness then upgrades quasi-finiteness to finiteness.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace FLT.Mazur.GeometricSectionQuasiFinite

universe u
variable {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]

/-- Finitely many maps on every algebraically closed geometric test force quasi-finiteness. -/
theorem locallyQuasiFinite
    (h : ∀ (K : Type u) [Field K] [IsAlgClosed K] (g : Spec (.of K) ⟶ S),
      Finite (Over.mk g ⟶ Over.mk f)) : LocallyQuasiFinite f := by
  apply LocallyQuasiFinite.of_finite_preimage_singleton
  intro s
  let K := AlgebraicClosure (S.residueField s)
  let g : Spec (.of K) ⟶ Spec (S.residueField s) :=
    Spec.map (CommRingCat.ofHom (algebraMap (S.residueField s) K))
  let a := f.fiberToSpecResidueField s
  have : Surjective g := ⟨Function.surjective_to_subsingleton _⟩
  have : Finite (Over.mk (g ≫ S.fromSpecResidueField s) ⟶ Over.mk f) :=
    h K (g ≫ S.fromSpecResidueField s)
  have : Finite (Over.mk g ⟶ Over.mk a) :=
    Finite.of_injective _
      (BaseChangeSectionEquiv.post_base_injective f (S.fromSpecResidueField s) g)
  have : Finite {p : Spec (.of K) ⟶ pullback a g // p ≫ pullback.snd a g = 𝟙 _} :=
    Finite.of_equiv _ (BaseChangeSectionEquiv.equiv a g).symm
  have : LocallyOfFiniteType a := by
    dsimp [a, Scheme.Hom.fiberToSpecResidueField]
    infer_instance
  have : Finite (pullback a g : Scheme) := FiniteGeometricSections.finite_carrier (pullback.snd a g)
  have : Finite (f.fiber s) := Finite.of_surjective _ (pullback.fst a g).surjective
  rw [← f.range_fiberι s]
  exact Set.finite_range _

omit [LocallyOfFiniteType f] in
/-- A proper scheme with finite geometric relative point sets is finite over its base. -/
theorem isFinite [IsProper f]
    (h : ∀ (K : Type u) [Field K] [IsAlgClosed K] (g : Spec (.of K) ⟶ S),
      Finite (Over.mk g ⟶ Over.mk f)) : IsFinite f := by
  have := locallyQuasiFinite f h
  exact IsFinite.of_isProper_of_locallyQuasiFinite f

end FLT.Mazur.GeometricSectionQuasiFinite
