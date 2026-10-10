/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.IncreasingCechFlatKernels
public import FLT.Mazur.FlatCoefficientAllCohomology

/-!
# Arbitrary affine base change from cohomological flatness

Flat Cech terms and flat positive sheaf cohomology give flat global sections
and base change for every affine coefficient map, including nonflat ones.
The comparison is built from the canonical tensor-kernel map and actual gluing.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry TensorProduct
open Scheme.Modules hiding map_smul
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.IncreasingCechCoefficients
open IncreasingCechScalars FCurve Chow

variable {P X T S : Scheme.{0}} [IsAffine T] [IsAffine S] [X.IsSeparated]
  {p : P ⟶ X} {q : P ⟶ T} {f : X ⟶ S} {g : T ⟶ S}
  (h : IsPullback p q f g) (M : X.Modules) [M.IsQuasicoherent]
  {ι : Type} [LinearOrder ι] [Finite ι] (U : ι → X.Opens)
  (hU : ∀ i, IsAffineOpen (U i)) (hCover : iSup U = ⊤)
  [∀ n, Module.Flat Γ(S, ⊤) (BaseTerm M U f.appTop.hom n)]
  (hH : ∀ n, Module.Flat Γ(S, ⊤) (ModuleRingH f.appTop.hom M (n + 1)))

omit [IsAffine S] [Finite ι]
  [∀ n, Module.Flat Γ(S, ⊤) (BaseTerm M U f.appTop.hom n)] in
include hU hCover hH in
/-- The hypotheses on actual sheaf cohomology make the actual bounded cohomology flat. -/
theorem baseHomology_flat_of_ringH (n : ℕ) :
    Module.Flat Γ(S, ⊤) (BaseHomology M U f.appTop.hom (n + 1)) := by
  let _ := hH n
  exact Module.Flat.of_linearEquiv
    (affineRingCohomologyEquiv M U hU hCover f.appTop.hom (n + 1))

omit [IsAffine S] in
include hU hCover hH in
/-- Global sections are flat under the bounded cohomological criterion. -/
theorem sections_flat_of_positive_ringH :
    Module.Flat Γ(S, ⊤) (baseSections M f.appTop.hom ⊤) :=
  baseSections_flat_of_positive_flat M U f.appTop.hom
    (baseHomology_flat_of_ringH M U hU hCover hH) hCover

/-- Arbitrary affine coefficient extension preserves the actual global sections. -/
def cohomologicallyFlatSectionsEquiv :
    let _ : Algebra Γ(S, ⊤) Γ(T, ⊤) := g.appTop.hom.toAlgebra
    Γ(T, ⊤) ⊗[Γ(S, ⊤)] baseSections M f.appTop.hom ⊤ ≃ₗ[Γ(T, ⊤)]
      baseSections ((pullback p).obj M) q.appTop.hom ⊤ := by
  let _ : Algebra Γ(S, ⊤) Γ(T, ⊤) := g.appTop.hom.toAlgebra
  let e := LinearEquiv.ofBijective
    (LinearMap.tensorKer Γ(T, ⊤) Γ(T, ⊤) (baseD M U f.appTop.hom 0))
    (baseD_tensorKer_bijective M U f.appTop.hom
      (baseHomology_flat_of_ringH M U hU hCover hH) 0 Γ(T, ⊤))
  exact (AlgebraTensorModule.congr (LinearEquiv.refl Γ(T, ⊤) Γ(T, ⊤))
    (baseSectionsZeroKernelEquiv M U f.appTop.hom hCover)).trans
      (e.trans (tensorKernelSectionsEquiv h M U hU hCover))

/-- The same arbitrary affine comparison in the actual derived H0 convention. -/
def cohomologicallyFlatHZeroEquiv :
    let _ : Algebra Γ(S, ⊤) Γ(T, ⊤) := g.appTop.hom.toAlgebra
    Γ(T, ⊤) ⊗[Γ(S, ⊤)] ModuleRingH f.appTop.hom M 0 ≃ₗ[Γ(T, ⊤)]
      ModuleRingH q.appTop.hom ((pullback p).obj M) 0 := by
  let _ : Algebra Γ(S, ⊤) Γ(T, ⊤) := g.appTop.hom.toAlgebra
  exact (AlgebraTensorModule.congr (LinearEquiv.refl Γ(T, ⊤) Γ(T, ⊤))
    (ringHZeroBaseSections M f.appTop.hom)).trans
      ((cohomologicallyFlatSectionsEquiv h M U hU hCover hH).trans
        (ringHZeroBaseSections ((pullback p).obj M) q.appTop.hom).symm)

end FLT.Mazur.IncreasingCechCoefficients
