/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
public import Mathlib.CategoryTheory.Sites.SubcanonicalOver
public import Mathlib.CategoryTheory.Sites.LocallySurjective

/-!
# A relative fppf scheme cover is locally surjective on represented sheaves

The proof uses the actual scheme pullback over each relative test. Thus local
lifts come from a geometric covering family, without a sheaf-effectivity assumption.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.RelativeFppfRepresentedCover
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {S : Scheme} {U Z : Over S} (a : U ⟶ Z)
  [Flat a.left] [Surjective a.left] [LocallyOfFinitePresentation a.left]

/-- A single relative fppf morphism is an actual covering family in the relative site. -/
theorem covering : Sieve.ofArrows (fun _ : Unit ↦ U) (fun _ ↦ a) ∈
    (Scheme.fppfTopology.over S) Z := by
  rw [GrothendieckTopology.mem_over_iff, Sieve.overEquiv_ofArrows]
  apply Precoverage.generate_mem_toGrothendieck
  exact (Scheme.Cover.mkOfCovers (P := @Flat ⊓ @LocallyOfFinitePresentation)
    (X := Z.left) Unit (fun _ ↦ U.left) (fun _ ↦ a.left)
    (fun z ↦ ⟨(), (a.left.surjective z).choose, (a.left.surjective z).choose_spec⟩)
    (fun _ ↦ ⟨inferInstance, inferInstance⟩)).mem₀

/-- Local lifts to a represented relative fppf cover exist on every original test. -/
theorem isLocallySurjective :
    Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S) (uliftYoneda.{1}.map a) where
  imageSieve_mem {T} t := by
    let b := pullback.snd a t.down
    have H := (IsPullback.of_hasPullback a t.down).map (Over.forget S)
    let _ : Flat b.left :=
      MorphismProperty.of_isPullback H (inferInstanceAs (Flat a.left))
    let _ : Surjective b.left :=
      MorphismProperty.of_isPullback H (inferInstanceAs (Surjective a.left))
    let _ : LocallyOfFinitePresentation b.left :=
      MorphismProperty.of_isPullback H (inferInstanceAs (LocallyOfFinitePresentation a.left))
    have hc := covering b
    apply (Scheme.fppfTopology.over S).superset_covering _ hc
    intro W g hg
    obtain ⟨i, k, rfl⟩ := Sieve.ofArrows.exists hg
    refine ⟨ULift.up (k ≫ pullback.fst a t.down), ?_⟩
    apply ULift.ext
    change (k ≫ pullback.fst a t.down) ≫ a = (k ≫ b) ≫ t.down
    dsimp only [b]
    rw [Category.assoc, pullback.condition, Category.assoc]

/-- The same geometric cover gives local surjectivity in the original sheaf category. -/
theorem sheaf_isLocallySurjective :
    Sheaf.IsLocallySurjective ((Scheme.fppfTopology.over S).uliftYoneda.{1}.map a) :=
  isLocallySurjective a

end FLT.Mazur.RelativeFppfRepresentedCover
