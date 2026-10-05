/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteIntersectionSectionDiagram

/-!
# Ambient sections and finite intersection coordinates

The top-section isomorphism identifies ambient sections on each intersection
with its coordinate algebra. It respects restriction and the structural map
from the affine base.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.Approximation

universe u v

variable {A : Type u} [CommRing A] {X : Scheme.{u}} {ι : Type v}
  (U : ι → X.Opens) (p : X ⟶ Spec (.of A))

/-- Ambient sections are the coordinate ring of the actual open subscheme. -/
def finiteIntersectionSectionEquiv (s : NonemptyChartSet ι) :
    Γ(X, finiteIntersectionOpen U s) ≃+* (finiteIntersectionSectionDiagram U p).obj s :=
  (finiteIntersectionOpen U s).topIso.symm.commRingCatIsoToRingEquiv

/-- The comparison carries ambient restrictions to coordinate restriction maps. -/
theorem finiteIntersectionSectionEquiv_naturality {s t : NonemptyChartSet ι}
    (f : s ⟶ t) (x : Γ(X, finiteIntersectionOpen U s)) :
    ((finiteIntersectionSectionDiagram U p).map f).hom
        (finiteIntersectionSectionEquiv U p s x) =
      finiteIntersectionSectionEquiv U p t
        (X.presheaf.map (homOfLE (finiteIntersectionOpen_antitone U (leOfHom f))).op x) := by
  have h := X.restrictFunctorΓ.inv.naturality
    (homOfLE (finiteIntersectionOpen_antitone U (leOfHom f))).op
  exact (congrArg (fun k ↦ k x) h).symm

/-- The affine-base structure on ambient sections, using the actual structural morphism. -/
abbrev finiteIntersectionAmbientAlgebra (s : NonemptyChartSet ι) :
    Algebra A Γ(X, finiteIntersectionOpen U s) :=
  ((finiteIntersectionSectionEquiv U p s).symm.toRingHom.comp
    (algebraMap A ((finiteIntersectionSectionDiagram U p).obj s))).toAlgebra

/-- The transported scalar is restriction of the actual global structural section. -/
theorem finiteIntersectionAmbientAlgebra_scalar (s : NonemptyChartSet ι) (a : A) :
    letI := finiteIntersectionAmbientAlgebra U p s
    algebraMap A Γ(X, finiteIntersectionOpen U s) a =
      X.presheaf.map (homOfLE (show finiteIntersectionOpen U s ≤ ⊤ from le_top)).op
        (affineBaseSectionMap p a) := by
  change (finiteIntersectionOpen U s).topIso.hom
    (((finiteIntersectionOpen U s).ι ≫ p).appTop ((Scheme.ΓSpecIso (.of A)).inv a)) = _
  rw [Scheme.Hom.comp_appTop]
  simp only [CommRingCat.comp_apply, Scheme.Opens.ι_appTop, Scheme.Opens.topIso_hom,
    affineBaseSectionMap, RingHom.comp_apply]
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

/-- The ring comparison also respects the affine-base algebra structures. -/
def finiteIntersectionSectionAlgEquiv (s : NonemptyChartSet ι) :
    letI := finiteIntersectionAmbientAlgebra U p s
    Γ(X, finiteIntersectionOpen U s) ≃ₐ[A] (finiteIntersectionSectionDiagram U p).obj s := by
  letI := finiteIntersectionAmbientAlgebra U p s
  exact { finiteIntersectionSectionEquiv U p s with
    commutes' := fun a ↦ (finiteIntersectionSectionEquiv U p s).apply_symm_apply _ }

end FLT.Mazur.Approximation
