/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FlatGlobalFunctionBaseChange
public import FLT.Mazur.FlatAlgebraEqualizerNaturality

/-!
# Naturality of geometric ground change for global functions

The multiplicative comparison commutes with every morphism over the base.
Applied to the two endpoints of a relation, these are the actual geometric
endpoint squares needed to compare tensor invariants with geometric invariants.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry TensorProduct
namespace FLT.Mazur.SchemeFunctionGroundChange
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {S T : Scheme.{0}}

/-- Structural algebras on global functions of objects over a scheme. -/
abbrev sectionAlgebra {Z : Scheme} (Y : Over Z) : Algebra Γ(Z, ⊤) Γ(Y.left, ⊤) :=
  FlatGlobalFunctionBaseChange.sectionAlgebra Y.hom

attribute [local instance] sectionAlgebra

/-- A geometric map over the base induces the original structural algebra map. -/
def sectionMap {X Y : Over S} (a : X ⟶ Y) : Γ(Y.left, ⊤) →ₐ[Γ(S, ⊤)] Γ(X.left, ⊤) :=
  ⟨a.left.appTop.hom, fun r ↦ by
    change a.left.appTop (Y.hom.appTop r) = X.hom.appTop r
    have h := congrArg (fun k ↦ k.appTop r) a.w
    exact h⟩

variable (g : T ⟶ S) {X Y : Over S} {P Q : Over T}
  {p : P.left ⟶ X.left} {q : Q.left ⟶ Y.left}
  (hP : IsPullback p P.hom X.hom g) (hQ : IsPullback q Q.hom Y.hom g)

/-- The global comparison on an actual geometric ground change. -/
def comparison :
    let _ := FlatGlobalFunctionBaseChange.sectionAlgebra g
    Γ(T, ⊤) ⊗[Γ(S, ⊤)] Γ(X.left, ⊤) →ₐ[Γ(T, ⊤)] Γ(P.left, ⊤) :=
  FlatGlobalFunctionBaseChange.comparison hP

/-- On pure tensors the comparison is scalar multiplication of geometric pullback. -/
theorem comparison_tmul (b : Γ(T, ⊤)) (a : Γ(X.left, ⊤)) :
    let _ := FlatGlobalFunctionBaseChange.sectionAlgebra g
    comparison g hP (b ⊗ₜ[Γ(S, ⊤)] a) = P.hom.appTop b * p.appTop a := rfl

variable (a : X ⟶ Y) (b : P ⟶ Q) (w : b.left ≫ q = p ≫ a.left)

include w in
/-- Tensor comparison commutes with the actual map on global functions. -/
theorem comparison_natural :
    let _ := FlatGlobalFunctionBaseChange.sectionAlgebra g
    ∀ x : Γ(T, ⊤) ⊗[Γ(S, ⊤)] Γ(Y.left, ⊤),
      comparison g hP (FlatAlgebraEqualizer.tensorMap Γ(T, ⊤) (sectionMap a) x) =
        sectionMap b (comparison g hQ x) := by
  let _ := FlatGlobalFunctionBaseChange.sectionAlgebra g
  dsimp only
  intro x
  induction x using TensorProduct.inductionOn with
  | tmul r y =>
    change P.hom.appTop r * p.appTop (a.left.appTop y) =
      b.left.appTop (Q.hom.appTop r * q.appTop y)
    rw [map_mul]
    have hb := congrArg (fun k ↦ k.appTop r) b.w
    have hw := congrArg (fun k ↦ k.appTop y) w
    change b.left.appTop (Q.hom.appTop r) = P.hom.appTop r at hb
    change b.left.appTop (q.appTop y) = p.appTop (a.left.appTop y) at hw
    rw [hb, hw]
  | add x y hx hy => simp only [map_add, hx, hy]

variable [CompactSpace X.left] [X.left.IsSeparated] [IsAffine T] [IsAffine S] [Flat g]

/-- Global tensor functions identify with actual functions after flat affine ground change. -/
def sectionsEquiv :
    let _ := FlatGlobalFunctionBaseChange.sectionAlgebra g
    Γ(T, ⊤) ⊗[Γ(S, ⊤)] Γ(X.left, ⊤) ≃ₐ[Γ(T, ⊤)] Γ(P.left, ⊤) :=
  FlatGlobalFunctionBaseChange.sectionsEquiv hP

/-- The geometric function equivalence retains the canonical comparison map. -/
theorem sectionsEquiv_apply :
    let _ := FlatGlobalFunctionBaseChange.sectionAlgebra g
    ∀ x : Γ(T, ⊤) ⊗[Γ(S, ⊤)] Γ(X.left, ⊤),
      sectionsEquiv g hP x = comparison g hP x := fun _ ↦ rfl

end FLT.Mazur.SchemeFunctionGroundChange
