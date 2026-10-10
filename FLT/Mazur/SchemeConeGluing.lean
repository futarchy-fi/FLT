/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CofinalUpperLimit
public import Mathlib.AlgebraicGeometry.Gluing

/-!
# Gluing locally constructed inverse-limit lifts

For a cone with a monic projection, local lifts are automatically compatible.
It suffices to construct them over an open cover, checking their components
on the cofinal upper interval above one fixed stage.
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry

namespace FLT.Mazur.Approximation

universe u v

variable {I : Type v} [Preorder I] [IsDirectedOrder I]
  {F : Iᵒᵖ ⥤ Scheme.{u}} (c : Cone F) (i : I)

/-- Factorization on all stages above a fixed stage implies factorization everywhere. -/
theorem cone_fac_of_upper (s : Cone F) {Y : Scheme.{u}} (p : Y ⟶ s.pt) (g : Y ⟶ c.pt)
    (h : ∀ j : Set.Ici i, g ≫ c.π.app (.op j.val) = p ≫ s.π.app (.op j.val)) (j : I) :
    g ≫ c.π.app (.op j) = p ≫ s.π.app (.op j) := by
  obtain ⟨k, hik, hjk⟩ := exists_ge_ge i j
  calc
    g ≫ c.π.app (.op j) =
        (g ≫ c.π.app (.op k)) ≫ F.map (homOfLE hjk).op := by rw [Category.assoc, c.w]
    _ = (p ≫ s.π.app (.op k)) ≫ F.map (homOfLE hjk).op := by rw [h ⟨k, hik⟩]
    _ = p ≫ s.π.app (.op j) := by rw [Category.assoc, s.w]

variable [Mono (c.π.app (.op i))]

/-- Local upper-stage lifts into a cone glue to a global lift. -/
def schemeConeGluedLift (s : Cone F) (V : s.pt.OpenCover.{u})
    (g : ∀ k, V.X k ⟶ c.pt)
    (hg : ∀ k (j : Set.Ici i), g k ≫ c.π.app (.op j.val) = V.f k ≫ s.π.app (.op j.val)) :
    s.pt ⟶ c.pt :=
  V.glueMorphisms g (by
    intro k l
    apply (cancel_mono (c.π.app (.op i))).1
    rw [Category.assoc, Category.assoc, hg k ⟨i, le_rfl⟩, hg l ⟨i, le_rfl⟩,
      ← Category.assoc, ← Category.assoc, pullback.condition])

/-- The glued lift factors every component of the test cone. -/
@[reassoc] theorem schemeConeGluedLift_fac (s : Cone F) (V : s.pt.OpenCover.{u})
    (g : ∀ k, V.X k ⟶ c.pt)
    (hg : ∀ k (j : Set.Ici i), g k ≫ c.π.app (.op j.val) = V.f k ≫ s.π.app (.op j.val))
    (j : I) :
    schemeConeGluedLift c i s V g hg ≫ c.π.app (.op j) = s.π.app (.op j) := by
  apply V.hom_ext
  intro k
  rw [← Category.assoc]
  change (V.f k ≫ V.glueMorphisms g _) ≫ _ = _
  rw [V.ι_glueMorphisms]
  exact cone_fac_of_upper c i s (V.f k) (g k) (hg k) j

/-- Open-cover existence of upper-stage lifts proves the full universal property. -/
def schemeConeIsLimitOfLocalLifts
    (V : ∀ s : Cone F, s.pt.OpenCover.{u})
    (g : ∀ (s : Cone F) k, (V s).X k ⟶ c.pt)
    (hg : ∀ (s : Cone F) k (j : Set.Ici i),
      g s k ≫ c.π.app (.op j.val) = (V s).f k ≫ s.π.app (.op j.val)) : IsLimit c where
  lift s := schemeConeGluedLift c i s (V s) (g s) (hg s)
  fac s j := schemeConeGluedLift_fac c i s (V s) (g s) (hg s) j.unop
  uniq s m hm := by
    apply (cancel_mono (c.π.app (.op i))).1
    exact (hm (.op i)).trans (schemeConeGluedLift_fac c i s (V s) (g s) (hg s) i).symm

end FLT.Mazur.Approximation
