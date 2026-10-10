/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FlatCoefficientSections
public import FLT.Mazur.FlatCoefficientCohomology

/-!
# Flat affine base change in every cohomological degree

Degree zero is compared through actual global sections; positive degrees use
the actual adjacent Cech complexes. Both retain the specified base-ring actions.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry TensorProduct
open Scheme.Modules hiding map_smul
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.IncreasingCechCoefficients
open IncreasingCechScalars FCurve Chow

/-- The H0 comparison with the section convention used by the Cech complex. -/
def ringHZeroBaseSections {X : Scheme.{0}} (M : X.Modules) {R : Type} [CommRing R]
    (ρ : R →+* Γ(X, ⊤)) : ModuleRingH ρ M 0 ≃ₗ[R] baseSections M ρ ⊤ :=
  { (moduleH0Equiv M).toAddEquiv with
    map_smul' := fun r x ↦ by
      change (moduleH0Equiv M) (ρ r • (show ModuleH M 0 from x)) =
        X.presheaf.map (𝟙 _) (ρ r) • (moduleH0Equiv M) x
      rw [LinearEquiv.map_smul, CategoryTheory.Functor.map_id]
      rfl }

variable {P X T S : Scheme.{0}} [IsAffine T] [IsAffine S] [X.IsSeparated]
  {p : P ⟶ X} {q : P ⟶ T} {f : X ⟶ S} {g : T ⟶ S}
  (h : IsPullback p q f g) (M : X.Modules) [M.IsQuasicoherent]
  {ι : Type} [LinearOrder ι] [Finite ι] (U : ι → X.Opens)
  (hU : ∀ i, IsAffineOpen (U i)) (hCover : iSup U = ⊤)

/-- Flat affine change of base preserves actual quasi-coherent H0 with its scalar action. -/
def flatZeroCohomologyEquiv (hg : g.appTop.hom.Flat) :
    let _ : Algebra Γ(S, ⊤) Γ(T, ⊤) := g.appTop.hom.toAlgebra
    Γ(T, ⊤) ⊗[Γ(S, ⊤)] ModuleRingH f.appTop.hom M 0 ≃ₗ[Γ(T, ⊤)]
      ModuleRingH q.appTop.hom ((pullback p).obj M) 0 := by
  let _ : Algebra Γ(S, ⊤) Γ(T, ⊤) := g.appTop.hom.toAlgebra
  exact (AlgebraTensorModule.congr (LinearEquiv.refl Γ(T, ⊤) Γ(T, ⊤))
    (ringHZeroBaseSections M f.appTop.hom)).trans
      ((flatSectionsEquiv h M U hU hCover hg).trans
        (ringHZeroBaseSections ((pullback p).obj M) q.appTop.hom).symm)

/-- Flat affine change of base commutes with every actual quasi-coherent cohomology group. -/
def flatCohomologyEquiv (hg : g.appTop.hom.Flat) (n : ℕ) :
    let _ : Algebra Γ(S, ⊤) Γ(T, ⊤) := g.appTop.hom.toAlgebra
    Γ(T, ⊤) ⊗[Γ(S, ⊤)] ModuleRingH f.appTop.hom M n ≃ₗ[Γ(T, ⊤)]
      ModuleRingH q.appTop.hom ((pullback p).obj M) n := by
  cases n with
  | zero => exact flatZeroCohomologyEquiv h M U hU hCover hg
  | succ n => exact flatPositiveCohomologyEquiv h M U hU hCover hg n

end FLT.Mazur.IncreasingCechCoefficients
