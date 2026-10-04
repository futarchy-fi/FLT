/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ClassifiedGenusOneFamily
public import FLT.Mazur.PolygonActionBaseChange

/-!
# The geometric rotation condition for generalized elliptic curves

DR II.1.12(c) concerns every rational point of the actual pulled-back group.
Vertices are all irreducible components; edges are all nonsmooth points.
One cyclic indexing simultaneously describes incidence and all translations.
The indexing retains distinct edges for the two-gon and the loop for the one-gon.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
open TopologicalSpace
namespace FLT.Mazur.GeneralizedCurveGraph

/-- Specialize an action at a rational point of its group. -/
def translation {S : Scheme} {G X : Over S} (act : G ⊗ X ⟶ X)
    (x : 𝟙_ (Over S) ⟶ G) : X ⟶ X :=
  (λ_ X).inv ≫ x ▷ X ≫ act

/-- A cyclic indexing of the actual graph in which every translation is a rotation. -/
def Rotations {L : Type} [Field L] {G X : Over (Spec (.of L))}
    [LocallyOfFinitePresentation X.hom] (act : G ⊗ X ⟶ X) : Prop :=
  ∃ (n : ℕ) (hn : 0 < n),
    letI : NeZero n := ⟨Nat.ne_of_gt hn⟩
    ∃ (v : Fin n ≃ irreducibleComponents X.left)
      (e : Fin n ≃ {z : X.left // z ∉ X.hom.smoothLocus}),
      (∀ i j, (e j).val ∈ (v i).val ↔ i = j ∨ i = PolygonPinching.next hn j) ∧
      ∀ x : 𝟙_ (Over (Spec (.of L))) ⟶ G,
        ∃ b : ZMod n, (∀ i, (translation act x).left '' (v i).val =
          (v (PolygonPinching.rotateIndex b i)).val) ∧
          ∀ j, (translation act x).left (e j).val =
            (e (PolygonPinching.rotateIndex b j)).val

/-- Rotations on one actual field-valued pullback. -/
def FiberRotations {S : Scheme} {G X : Over S}
    [LocallyOfFinitePresentation X.hom] (act : G ⊗ X ⟶ X)
    {L : Type} [Field L] (g : Spec (.of L) ⟶ S) : Prop :=
  letI : LocallyOfFinitePresentation ((Over.pullback g).obj X).hom :=
    inferInstanceAs (LocallyOfFinitePresentation (pullback.snd X.hom g))
  Rotations (Functor.LaxMonoidal.μ (Over.pullback g) G X ≫ (Over.pullback g).map act)

/-- DR's rotation requirement on every singular geometric fiber, using actual pullback. -/
def GeometricRotations {S : Scheme} {G X : Over S}
    [LocallyOfFinitePresentation X.hom] (act : G ⊗ X ⟶ X) : Prop :=
  ∀ (L : Type) [Field L] [IsAlgClosed L] (g : Spec (.of L) ⟶ S),
    ¬ Smooth ((Over.pullback g).obj X).hom → FiberRotations act g

end FLT.Mazur.GeneralizedCurveGraph
