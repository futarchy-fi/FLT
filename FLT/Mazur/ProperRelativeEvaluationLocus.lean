/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteEvaluationLocus
public import FLT.Mazur.ProperGlobalSectionFinite

/-!
# The open locus of scalar-extended proper evaluation

The section gives an augmentation of the actual proper global-function ring.
Proper cohomology makes this ring finite over a Noetherian affine base, so
injectivity of its residue-field scalar extensions is an open condition.
This does not identify scalar-extended functions with functions on a geometric
fiber; a nonflat cohomology base-change theorem is still needed for that step.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.Approximation

open FLT.Mazur.Chow.AffineBase

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {R : CommRingCat.{0}} {X : Scheme.{0}} (f : X ⟶ Spec R)
  (s : Spec R ⟶ X) (hs : s ≫ f = 𝟙 _)

/-- Section evaluation as an augmentation for the original structural algebra action. -/
def relativeSectionAugmentation :
    let _ := (baseCohomologyScalars f).toAlgebra
    Γ(X, ⊤) →ₐ[R] R :=
  let _ := (baseCohomologyScalars f).toAlgebra
  { toRingHom := (s.appTop ≫ (Scheme.ΓSpecIso R).hom).hom
    commutes' r := by
      change ((Scheme.ΓSpecIso R).inv ≫ f.appTop ≫ s.appTop ≫
        (Scheme.ΓSpecIso R).hom) r = r
      rw [← Category.assoc f.appTop, ← Scheme.Hom.comp_appTop, hs]
      simp }

/-- The augmentation is literal evaluation followed by the canonical affine comparison. -/
theorem relativeSectionAugmentation_apply (a : Γ(X, ⊤)) :
    relativeSectionAugmentation f s hs a = (Scheme.ΓSpecIso R).hom (s.appTop a) := rfl

/-- Proper finiteness gives an open locus for injective scalar-extended evaluations. -/
theorem isOpen_proper_relativeEvaluationLocus [IsNoetherianRing R] [IsProper f] :
    let _ := (baseCohomologyScalars f).toAlgebra
    IsOpen {p : PrimeSpectrum R | Function.Injective
      ((relativeSectionAugmentation f s hs).toLinearMap.lTensor p.asIdeal.ResidueField)} := by
  let _ := (baseCohomologyScalars f).toAlgebra
  have := FLT.Mazur.ProperGlobalSectionFinite.finite f
  exact isOpen_residueAugmentationLocus (relativeSectionAugmentation f s hs)

end FLT.Mazur.Approximation
