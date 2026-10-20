/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteFreeEtaleTraceUnit
public import FLT.Mazur.AffineCartesianTrace
public import Mathlib.AlgebraicGeometry.Morphisms.Etale

/-!
# Surjectivity of the full affine étale trace

A geometric section induces a retraction of the actual section algebra. Finite
free étale trace surjectivity therefore applies to the unchanged morphism.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Module
namespace FLT.Mazur.AffineEtaleTraceSurjectivity
universe u v
variable {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y]
  (f : X ⟶ Y) (r : Y ⟶ X) (hr : r ≫ f = 𝟙 Y)

/-- A scheme section retracts the whole affine section algebra. -/
def sectionRetraction :
    let _ := f.appTop.hom.toAlgebra
    Γ(X, ⊤) →ₐ[Γ(Y, ⊤)] Γ(Y, ⊤) := by
  let _ := f.appTop.hom.toAlgebra
  exact { r.appTop.hom with
    commutes' := fun a ↦ by
      change (r ≫ f).appTop a = a
      rw [hr]
      rfl }

/-- Étaleness of the morphism is étaleness of its actual affine section algebra. -/
theorem sectionAlgebra_etale [Etale f] :
    let _ := f.appTop.hom.toAlgebra
    Algebra.Etale Γ(Y, ⊤) Γ(X, ⊤) := by
  let _ := f.appTop.hom.toAlgebra
  exact (HasRingHomProperty.iff_of_isAffine (P := @Etale) (f := f)).mp inferInstance

variable [Etale f] {ι : Type v} [Finite ι]

include hr in
/-- A finite basis and the actual geometric section construct a surjective full trace. -/
theorem sectionTrace_surjective :
    let _ := f.appTop.hom.toAlgebra
    Basis ι Γ(Y, ⊤) Γ(X, ⊤) →
      Function.Surjective (AffineCartesianTrace.sectionTrace f) := by
  let _ := f.appTop.hom.toAlgebra
  dsimp only
  intro basis
  let _ := Module.Free.of_basis basis
  let _ := Module.Finite.of_basis basis
  let _ := sectionAlgebra_etale f
  exact FiniteFreeEtaleTraceUnit.trace_surjective Γ(Y, ⊤) Γ(X, ⊤)
    (sectionRetraction f r hr)

end FLT.Mazur.AffineEtaleTraceSurjectivity
