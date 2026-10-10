/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CartesianStructurePositiveHomology

/-!
# Flat affine comparison for actual positive structure cohomology

The affine-cover comparison transports the cartesian bounded-complex theorem
to sheaf cohomology, retaining the structural actions of both affine base rings.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry TensorProduct
open scoped TensorProduct
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.IncreasingCechCartesian
open IncreasingCechScalars FCurve
variable {P X T S : Scheme.{0}} [IsAffine T] [IsAffine S]
  [X.IsSeparated]
  {p : P ⟶ X} {q : P ⟶ T} {f : X ⟶ S} {g : T ⟶ S}
  (h : IsPullback p q f g)
  {ι : Type} [LinearOrder ι] [Finite ι] (U : ι → X.Opens)
  (hU : ∀ i, IsAffineOpen (U i)) (hCover : iSup U = ⊤)

/-- The actual positive structure-sheaf cohomology comparison over the target affine ring. -/
def flatStructureCohomologyEquiv (hg : g.appTop.hom.Flat) (n : ℕ) :
    let _ : Algebra Γ(S, ⊤) Γ(T, ⊤) := g.appTop.hom.toAlgebra
    Γ(T, ⊤) ⊗[Γ(S, ⊤)] ModuleRingH f.appTop.hom (structureModule X) (n + 1) ≃ₗ[Γ(T, ⊤)]
      ModuleRingH q.appTop.hom (structureModule P) (n + 1) := by
  let _ : Algebra Γ(S, ⊤) Γ(T, ⊤) := g.appTop.hom.toAlgebra
  let _ : IsAffineHom p := MorphismProperty.of_isPullback h.flip inferInstance
  let _ : P.IsSeparated := ⟨by
    simpa only [Limits.terminal.comp_from] using
      (inferInstance : IsSeparated (p ≫ Limits.terminal.from X))⟩
  let _ : (structureModule X).IsFinitePresentation := unitSheaf_isFinitePresentation X
  let _ : (structureModule P).IsFinitePresentation := unitSheaf_isFinitePresentation P
  let a : BaseHomology (structureModule X) U f.appTop.hom (n + 1) ≃ₗ[Γ(S, ⊤)]
      ModuleRingH f.appTop.hom (structureModule X) (n + 1) :=
    affineRingCohomologyEquiv (structureModule X) U hU hCover f.appTop.hom (n + 1)
  let b : BaseHomology (structureModule P) (fun i ↦ p ⁻¹ᵁ U i) q.appTop.hom (n + 1) ≃ₗ[Γ(T, ⊤)]
      ModuleRingH q.appTop.hom (structureModule P) (n + 1) :=
    affineRingCohomologyEquiv (structureModule P) (fun i ↦ p ⁻¹ᵁ U i) (fun i ↦ (hU i).preimage p)
      (p.iSup_preimage_eq_top hCover) q.appTop.hom (n + 1)
  exact (AlgebraTensorModule.congr (LinearEquiv.refl Γ(T, ⊤) Γ(T, ⊤)) a.symm).trans
    ((flatGeometricPositiveHomologyIso h U hU hg n).toLinearEquiv.trans b)

end FLT.Mazur.IncreasingCechCartesian
