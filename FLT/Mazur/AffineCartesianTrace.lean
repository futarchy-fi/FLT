/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineCartesianNorm
public import FLT.Mazur.AffineEnvelopeNormTransport
public import Mathlib.RingTheory.Trace.Basic

/-!
# Traces of the full affine section algebra

Finite bases give cartesian trace transport. The trace itself is independent
of a displayed basis, and scalar multiplication remains in the original target.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Module TensorProduct
namespace FLT.Mazur.AffineCartesianTrace
universe u v
set_option backward.isDefEq.respectTransparency false
variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- Trace in the section algebra of the actual morphism. -/
def sectionTrace (s : Γ(X, ⊤)) : Γ(Y, ⊤) :=
  let _ := f.appTop.hom.toAlgebra
  Algebra.trace Γ(Y, ⊤) Γ(X, ⊤) s

/-- Trace is additive in the original section. -/
theorem sectionTrace_add (s t : Γ(X, ⊤)) :
    sectionTrace f (s + t) = sectionTrace f s + sectionTrace f t := by
  let _ := f.appTop.hom.toAlgebra
  exact map_add (Algebra.trace Γ(Y, ⊤) Γ(X, ⊤)) s t

/-- Target coefficients can be taken outside the trace. -/
theorem sectionTrace_mul (r : Γ(Y, ⊤)) (s : Γ(X, ⊤)) :
    sectionTrace f (f.appTop r * s) = r * sectionTrace f s := by
  let _ := f.appTop.hom.toAlgebra
  exact (Algebra.trace Γ(Y, ⊤) Γ(X, ⊤)).map_smul r s

/-- A scalar has trace equal to its multiple by the actual finite basis cardinality. -/
theorem sectionTrace_scalar {ι : Type v} [Fintype ι] :
    let _ := f.appTop.hom.toAlgebra
    ∀ (_b : Basis ι Γ(Y, ⊤) Γ(X, ⊤)) (r : Γ(Y, ⊤)),
      sectionTrace f (f.appTop r) = Fintype.card ι • r := by
  let _ := f.appTop.hom.toAlgebra
  exact fun b r ↦ Algebra.trace_algebraMap_of_basis b r

variable {P T : Scheme.{u}} [IsAffine X] [IsAffine Y] [IsAffine T]
  {a : P ⟶ X} {b : P ⟶ T} {g : T ⟶ Y} (H : IsPullback a b f g)

include H in
/-- Arbitrary cartesian base change preserves the whole section trace. -/
theorem sectionTrace_pullback {ι : Type v} [Finite ι] :
    let _ := f.appTop.hom.toAlgebra
    ∀ (_basis : Basis ι Γ(Y, ⊤) Γ(X, ⊤)) (s : Γ(X, ⊤)),
      sectionTrace b (a.appTop s) = g.appTop (sectionTrace f s) := by
  let _ := f.appTop.hom.toAlgebra
  let _ := g.appTop.hom.toAlgebra
  let _ := b.appTop.hom.toAlgebra
  dsimp only
  intro basis s
  let _ := Module.Free.of_basis basis
  let _ := Module.Finite.of_basis basis
  rw [← AffineCartesianNorm.tensorIso_right a b f g H]
  change Algebra.trace Γ(T, ⊤) Γ(P, ⊤)
    (AffineCartesianNorm.tensorAlgEquiv a b f g H (1 ⊗ₜ[Γ(Y, ⊤)] s)) = _
  rw [Algebra.trace_eq_of_algEquiv, Algebra.trace_apply,
    ← Algebra.baseChange_lmul, LinearMap.trace_baseChange]
  rfl

omit [IsAffine X] [IsAffine Y] [IsAffine T] in
/-- Isomorphic whole section algebras have the same trace. -/
theorem sectionTrace_transport {E F : Scheme.{u}} (p : E ⟶ T) (q : F ⟶ T)
    (i : E ≅ F) (hi : i.hom ≫ q = p) (s : Γ(F, ⊤)) :
    sectionTrace p (i.hom.appTop s) = sectionTrace q s := by
  let _ := p.appTop.hom.toAlgebra
  let _ := q.appTop.hom.toAlgebra
  exact Algebra.trace_eq_of_algEquiv
    (AffineEnvelopeNormTransport.sectionAlgEquiv p q i hi) s

end FLT.Mazur.AffineCartesianTrace
