/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.SectionCoverBaseChange

/-!
# Comparing section covers on two Cartesian coefficient models

The comparison retains the original source projection and the structure map.
It transports the entire section cover from the canonical pullback to the
specified second model, including every residue branch.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.CartesianSectionCoverTower
universe u v
variable {X Y Z S T U : Scheme.{u}}
  {a : Y ⟶ X} {b : Y ⟶ T} {f : X ⟶ S} {g : T ⟶ S}
  {c : Z ⟶ X} {d : Z ⟶ U} {h : U ⟶ T}
  (H : IsPullback a b f g) (J : IsPullback c d f (h ≫ g))

/-- The comparison to the first coefficient model retains both original projections. -/
def comparison : Z ⟶ Y := H.lift c (d ≫ h) (by simpa only [Category.assoc] using J.w)

/-- The first projection is the exact original source map. -/
@[reassoc] theorem comparison_original : comparison H J ≫ a = c := H.lift_fst _ _ _

/-- The comparison lies over the prescribed extension of coefficients. -/
@[reassoc] theorem comparison_structure : comparison H J ≫ b = d ≫ h := H.lift_snd _ _ _

/-- The second model is the base change of the first along the actual coefficient map. -/
theorem comparison_isPullback : IsPullback (comparison H J) d b h := by
  apply IsPullback.of_right (h₁₂ := a) (h₂₂ := g)
    (v₁₃ := f) _ (comparison_structure H J) H
  simpa only [comparison_original] using J

/-- Identify the specified second model with the canonical base change of the first. -/
def comparisonIso : Z ≅ pullback b h := (comparison_isPullback H J).isoPullback

/-- Transfer an actual section to the specified second model. -/
def sectionMap (r : U ⟶ pullback b h) : U ⟶ Z := r ≫ (comparisonIso H J).inv

/-- The transferred section retains its original projection to the first model. -/
@[reassoc] theorem sectionMap_original (r : U ⟶ pullback b h) :
    sectionMap H J r ≫ comparison H J = r ≫ pullback.fst b h := by
  exact Category.assoc _ _ _ |>.trans
    (congrArg (r ≫ ·) (comparison_isPullback H J).isoPullback_inv_fst)

/-- Its structure equation is exactly the original section equation. -/
@[reassoc] theorem sectionMap_structure (r : U ⟶ pullback b h) :
    sectionMap H J r ≫ d = r ≫ pullback.snd b h := by
  exact Category.assoc _ _ _ |>.trans
    (congrArg (r ≫ ·) (comparison_isPullback H J).isoPullback_inv_snd)

/-- Open sections remain open on the specified model. -/
theorem sectionMap_isOpenImmersion (r : U ⟶ pullback b h) [IsOpenImmersion r] :
    IsOpenImmersion (sectionMap H J r) := inferInstanceAs
  (IsOpenImmersion (r ≫ (comparisonIso H J).inv))

/-- Transport preserves coverage of the whole source, not only its rational points. -/
theorem sectionMap_covers {I : Type v} (r : I → (U ⟶ pullback b h))
    (hc : ∀ x : (pullback b h : Scheme.{u}), ∃ i z, r i z = x) :
    ∀ x : Z, ∃ i z, sectionMap H J (r i) z = x := by
  intro x
  obtain ⟨i, z, hz⟩ := hc ((comparisonIso H J).hom x)
  refine ⟨i, z, ?_⟩
  change (comparisonIso H J).inv (r i z) = x
  rw [hz]
  exact congrArg (fun m : Z ⟶ Z ↦ m x) (comparisonIso H J).hom_inv_id

end FLT.Mazur.CartesianSectionCoverTower
