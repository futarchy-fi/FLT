/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.IncreasingCechCoefficientKernel
public import Mathlib.RingTheory.Flat.Equalizer

/-!
# Flat base change for actual quasi-coherent global sections

Flatness identifies the tensor of the original zero-cycle kernel with the
kernel of the tensor differential. Actual sheaf gluing then identifies this
with sections of the actual pulled-back coefficient sheaf.
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

/-- Flat affine base change preserves actual global sections, with the target base action. -/
def flatSectionsEquiv (hg : g.appTop.hom.Flat) :
    let _ : Algebra Γ(S, ⊤) Γ(T, ⊤) := g.appTop.hom.toAlgebra
    Γ(T, ⊤) ⊗[Γ(S, ⊤)] baseSections M f.appTop.hom ⊤ ≃ₗ[Γ(T, ⊤)]
      baseSections ((pullback p).obj M) q.appTop.hom ⊤ := by
  let _ : Algebra Γ(S, ⊤) Γ(T, ⊤) := g.appTop.hom.toAlgebra
  let _ : Module.Flat Γ(S, ⊤) Γ(T, ⊤) := hg
  exact (AlgebraTensorModule.congr (LinearEquiv.refl Γ(T, ⊤) Γ(T, ⊤))
    (baseSectionsZeroKernelEquiv M U f.appTop.hom hCover)).trans
      ((LinearMap.tensorKerEquiv Γ(T, ⊤) Γ(T, ⊤) (baseD M U f.appTop.hom 0)).trans
        (tensorKernelSectionsEquiv h M U hU hCover))

end FLT.Mazur.IncreasingCechCoefficients
