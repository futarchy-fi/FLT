/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ProperPointExtension
public import Mathlib.AlgebraicGeometry.Morphisms.Finite

/-!
# Valuation extensions from finiteness of the full coefficient pullback

Only the full source after the specified base change must be finite. Its
properness extends each actual generic section, retaining its coefficient map.
Separated targets allow independent endpoint equations to extend as well.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R K : Type} [CommRing R] [IsDomain R] [ValuationRing R]
  [Field K] [Algebra R K] [IsFractionRing R K]
local notation "η" => Spec.map (CommRingCat.ofHom (algebraMap R K))

/-- Maps to a separated scheme are determined by their restriction to the fraction field. -/
theorem valuation_hom_ext {A : Scheme.{0}} [A.IsSeparated]
    {x y : Spec (.of R) ⟶ A} (h : η ≫ x = η ≫ y) : x = y := by
  let X := Over.mk (terminal.from A)
  let _ : IsSeparated X.hom := inferInstanceAs (IsSeparated (terminal.from A))
  let a : Points X (terminal.from (Spec (.of R))) :=
    Over.homMk x (terminal.hom_ext _ _)
  let b : Points X (terminal.from (Spec (.of R))) :=
    Over.homMk y (terminal.hom_ext _ _)
  have he : a = b := Points.valuation_precomp_injective X (K := K) _
    (Over.OverMorphism.ext h)
  exact congrArg (fun z ↦ z.left) he

/-- Full pullback finiteness constructs an extension of each generic source section. -/
theorem exists_valuation_extension_of_finite_pullback {D A : Scheme.{0}}
    (p : D ⟶ A) (x : Spec (.of R) ⟶ A)
    [IsFinite (pullback.snd p x)] (d : Spec (.of K) ⟶ D)
    (hd : d ≫ p = η ≫ x) :
    ∃ a : Spec (.of R) ⟶ D, η ≫ a = d ∧ a ≫ p = x := by
  let F := Over.mk (pullback.snd p x)
  let _ : IsProper F.hom := inferInstanceAs (IsProper (pullback.snd p x))
  let t : Points F (η ≫ 𝟙 (Spec (.of R))) :=
    Over.homMk (pullback.lift d η hd) (by
      change pullback.lift d η hd ≫ pullback.snd p x = η ≫ 𝟙 _
      rw [pullback.lift_snd, Category.comp_id])
  obtain ⟨a, ha, _⟩ := Points.existsUnique_valuation_extension F (𝟙 _) t
  have hag : η ≫ a.left = pullback.lift d η hd := congrArg (fun z ↦ z.left) ha
  have hap : a.left ≫ pullback.snd p x = 𝟙 (Spec (.of R)) := a.w
  refine ⟨a.left ≫ pullback.fst p x, ?_, ?_⟩
  · rw [← Category.assoc, hag, pullback.lift_fst]
  · rw [Category.assoc, pullback.condition, ← Category.assoc, hap, Category.id_comp]

/-- The constructed extension retains a second endpoint in any separated target. -/
theorem exists_valuation_two_endpoints_of_finite_pullback {D A B : Scheme.{0}}
    [B.IsSeparated] (p : D ⟶ A) (q : D ⟶ B)
    (x : Spec (.of R) ⟶ A) (y : Spec (.of R) ⟶ B)
    [IsFinite (pullback.snd p x)] (d : Spec (.of K) ⟶ D)
    (hx : d ≫ p = η ≫ x) (hy : d ≫ q = η ≫ y) :
    ∃ a : Spec (.of R) ⟶ D, η ≫ a = d ∧ a ≫ p = x ∧ a ≫ q = y := by
  obtain ⟨a, ha, hap⟩ := exists_valuation_extension_of_finite_pullback p x d hx
  refine ⟨a, ha, hap, valuation_hom_ext (K := K) ?_⟩
  rw [← Category.assoc, ha, hy]

end FLT.Mazur
