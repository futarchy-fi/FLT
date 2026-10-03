/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.PDivisibleSystem
public import Mathlib.CategoryTheory.Category.Basic

/-! # Morphisms of finite-flat p-divisible systems

Morphisms preserve the given integral inclusions and reductions. Composition
is contravariant on coordinate rings and covariant on the systems.
-/

@[expose] public noncomputable section
namespace ThreeAdicPlan.PDivisibleSystem
variable {R K : Type} [CommRing R] [IsLocalRing R] [Field K] [Algebra R K]
  [PerfectField K] [IsFractionRing R K] {p height : ℕ} [Fact p.Prime]

/-- A compatible family of integral level maps. -/
@[ext] structure Hom (X Y : PDivisibleSystem R K p height) where
  /-- The morphism on each finite flat level. -/
  app : ∀ n, ModelHom (X.level n) (Y.level n)
  inclusion_naturality : ∀ {m n} (h : m ≤ n),
    (X.inclusion h).comp (app n) = (app m).comp (Y.inclusion h)
  reduction_naturality : ∀ {m n} (h : m ≤ n),
    (X.reduction h).comp (app m) = (app n).comp (Y.reduction h)

/-- Identity on every coordinate ring. -/
def Hom.id (X : PDivisibleSystem R K p height) : Hom X X where
  app n := BialgHom.id R _
  inclusion_naturality _ := by ext; rfl
  reduction_naturality _ := by ext; rfl

/-- Compose compatible maps on their actual coordinate rings. -/
def Hom.comp {X Y Z : PDivisibleSystem R K p height} (f : Hom X Y) (g : Hom Y Z) :
    Hom X Z where
  app n := (f.app n).comp (g.app n)
  inclusion_naturality h := by
    rw [← BialgHom.comp_assoc, f.inclusion_naturality, BialgHom.comp_assoc,
      g.inclusion_naturality, ← BialgHom.comp_assoc]
  reduction_naturality h := by
    rw [← BialgHom.comp_assoc, f.reduction_naturality, BialgHom.comp_assoc,
      g.reduction_naturality, ← BialgHom.comp_assoc]

/-- The category of systems of a fixed height over the given base. -/
instance instCategory : CategoryTheory.Category (PDivisibleSystem R K p height) where
  Hom := Hom
  id := Hom.id
  comp := Hom.comp
  id_comp f := by ext n x; rfl
  comp_id f := by ext n x; rfl
  assoc f g h := by ext n x; rfl

end ThreeAdicPlan.PDivisibleSystem
