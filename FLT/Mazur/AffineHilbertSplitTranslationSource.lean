/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineHilbertTranslationFiberRelation
public import Mathlib.AlgebraicGeometry.Morphisms.FlatMono

/-!
# Original open sources constructed from split translation branches

Pull back an actual section of the etale translation along the original
parameter's translation coordinate. The resulting source is open in the
original source, over its unchanged ground. Its original relation is diagonal,
proved from the envelope and the section equation. Other branches remain open work.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart.AffineRestriction
open CartierAbel SchemePicard FCurve
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] relation fst snd
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R] {X : Scheme}
  (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  (d : ℕ) (V : Over (Spec (.of R))) [Etale V.hom]
  (c : (relativeFppfSheaf f).obj.obj (op V))
  {A : Over (Spec (.of R))} (k : A ⟶ variableHilbertTest f d V)
  [IsOpenImmersion k.left]
  (s : Over.mk (𝟙 (Spec (.of R))) ⟶ V)
local notation "β" => k ≫ variableHilbertBase f d V

omit [Algebra.FiniteType ℤ R] in
/-- An etale translation section is an actual open immersion over the original base. -/
theorem splitTranslation_section_isOpenImmersion : IsOpenImmersion s.left := by
  let _ : Etale (s.left ≫ V.hom) := by
    rw [s.w]
    exact inferInstanceAs (Etale (𝟙 (Spec (.of R))))
  let _ : Etale s.left := Etale.of_comp s.left V.hom
  let _ : IsSplitMono s.left := IsSplitMono.mk' ⟨V.hom, s.w⟩
  exact IsOpenImmersion.of_flat_of_mono s.left

/-- The constructed source retains its original family ground. -/
def splitTranslationSource : Over (Spec (.of R)) := pullback β s

/-- The source morphism is the actual translation pullback projection. -/
def splitTranslationSourceMap : splitTranslationSource f d V k s ⟶ A := pullback.fst β s

instance splitTranslationSourceMap_isOpenImmersion :
    IsOpenImmersion (splitTranslationSourceMap f d V k s).left := by
  exact MorphismProperty.of_isPullback
    ((IsPullback.of_hasPullback β s).map (Over.forget _)).flip
    (splitTranslation_section_isOpenImmersion V s)

/-- The new parameter is a genuine open selection of the ORIGINAL proper family. -/
def splitTranslationChart : splitTranslationSource f d V k s ⟶ variableHilbertTest f d V :=
  splitTranslationSourceMap f d V k s ≫ k

instance splitTranslationChart_isOpenImmersion :
    IsOpenImmersion (splitTranslationChart f d V k s).left := by
  change IsOpenImmersion ((splitTranslationSourceMap f d V k s).left ≫ k.left)
  infer_instance

local notation "l" => splitTranslationChart f d V k s
local notation "p" => fst f hL d V c l
local notation "q" => snd f hL d V c l

omit [Etale V.hom] [IsOpenImmersion k.left] in
/-- The original translation is invariant on the constructed slice, by its literal section map. -/
theorem splitTranslation_invariant :
    p ≫ l ≫ variableHilbertBase f d V = q ≫ l ≫ variableHilbertBase f d V := by
  have ht : p ≫ pullback.snd β s = q ≫ pullback.snd β s := by
    apply Over.OverMorphism.ext
    have hp := (p ≫ pullback.snd β s).w
    have hq := (q ≫ pullback.snd β s).w
    dsimp only [Over.mk_hom, Over.mk_left] at hp hq ⊢
    simpa only [Category.comp_id] using hp.trans hq.symm
  change p ≫ (pullback.fst β s ≫ k) ≫ variableHilbertBase f d V =
    q ≫ (pullback.fst β s ≫ k) ≫ variableHilbertBase f d V
  simp only [Category.assoc]
  rw [pullback.condition, ← Category.assoc, ht, Category.assoc]

/-- Both ORIGINAL endpoints agree on the constructed section slice, without full envelopes. -/
theorem splitTranslation_endpoints : p = q :=
  translationInvariant_endpoints f hL d V c l (splitTranslation_invariant f hL d V c k s)

omit [Etale V.hom] [IsOpenImmersion k.left] in
/-- Every original parameter on the chosen translation branch survives in the new source. -/
theorem splitTranslation_contains (x : A.left)
    (hx : (β).left x = s.left (A.hom x)) :
    ∃ y : (splitTranslationSource f d V k s).left,
      (splitTranslationSourceMap f d V k s).left y = x := by
  obtain ⟨y, hy, _⟩ := Scheme.exists_preimage_of_isPullback
    ((IsPullback.of_hasPullback β s).map (Over.forget _)) x (A.hom x) hx
  exact ⟨y, hy⟩

/-- The constructed source is affine when the original source and translation are affine. -/
instance splitTranslationSource_isAffine [IsAffine A.left] [IsAffine V.left] :
    IsAffine (splitTranslationSource f d V k s).left := by
  let _ : IsAffine (Over.mk (𝟙 (Spec (.of R)))).left :=
    inferInstanceAs (IsAffine (Spec (.of R)))
  let _ : IsAffineHom (splitTranslationSourceMap f d V k s).left :=
    MorphismProperty.of_isPullback
      ((IsPullback.of_hasPullback β s).map (Over.forget _)).flip
      (inferInstanceAs (IsAffineHom s.left))
  exact isAffine_of_isAffineHom (splitTranslationSourceMap f d V k s).left

end FLT.Mazur.HilbertChart.AffineRestriction
