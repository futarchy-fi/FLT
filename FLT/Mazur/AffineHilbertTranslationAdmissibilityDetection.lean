/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineHilbertTranslationSourceCoefficients

/-!
# Detecting original admissibility after surjective translation change

A surjective translation change gives a surjective independent envelope map.
Consequently membership of an ORIGINAL coefficient in its denominator ideal
is detected exactly after actual source pullback.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart.AffineRestriction
open CartierAbel SchemePicard FCurve SchemeEffectiveEpiSections
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
section Products
variable {S : Scheme} {A B C D : Over S} (a : A ⟶ B) (b : C ⟶ D)

/-- The second product coordinate gives the actual base change of a translation arrow. -/
theorem translationProductRight_isPullback :
    IsPullback (prod.snd : prod B C ⟶ C) (prod.map (𝟙 B) b) b
      (prod.snd : prod B D ⟶ D) := by
  refine IsPullback.of_isLimit (PullbackCone.IsLimit.mk (by simp)
    (fun z => prod.lift (z.snd ≫ prod.fst) z.fst)
    (fun z => by simp) (fun z => ?_) (fun z t ht he => ?_))
  · apply prod.hom_ext
    · simp
    · simpa using z.condition
  · apply prod.hom_ext
    · have H := congrArg (fun t => t ≫ prod.fst) he
      simpa using H
    · simpa using ht

/-- Independent surjective changes of the two coordinates cover their actual scheme product. -/
theorem translationProductMap_surjective [Surjective a.left] [Surjective b.left] :
    Surjective (prod.map a b).left := by
  let _ : Surjective (prod.map a (𝟙 C)).left :=
    MorphismProperty.of_isPullback
      ((IsPullback.of_prod_fst_with_id a C).map (Over.forget S))
      (inferInstanceAs (Surjective a.left))
  let _ : Surjective (prod.map (𝟙 B) b).left :=
    MorphismProperty.of_isPullback
      ((translationProductRight_isPullback (B := B) b).map (Over.forget S))
      (inferInstanceAs (Surjective b.left))
  have H : prod.map a b = prod.map a (𝟙 C) ≫ prod.map (𝟙 B) b := by
    apply prod.hom_ext <;> simp
  rw [H]
  change Surjective ((prod.map a (𝟙 C)).left ≫ (prod.map (𝟙 B) b).left)
  infer_instance
end Products

variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R] {X : Scheme}
  (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  (d : ℕ) {V W : Over (Spec (.of R))} (b : W ⟶ V)
  (c : (relativeFppfSheaf f).obj.obj (op V))
  {A : Over (Spec (.of R))} (k : A ⟶ variableHilbertTest f d V)
local notation "u" => translationSourceMap f d b k
local notation "l" => translationSourceChart f d b k
local notation "c'" => CategoryTheory.Functor.map
  (ObjectProperty.FullSubcategory.obj (relativeFppfSheaf f)) (Quiver.Hom.op b) c

local notation "C" => compatibleFunctions
  (Over.Hom.left (fst f hL d V c k)) (Over.Hom.left (snd f hL d V c k))

/-- A surjective translation change also covers the actual original source. -/
instance translationSourceMap_surjective [Surjective b.left] : Surjective (u).left :=
  translationSourceMap_property f d b k _ inferInstance

/-- The lower map of the Cartesian envelope square is surjective on scheme points. -/
theorem translationSourceEnvelope_surjective [Surjective b.left] :
    Surjective (prod.map u b).left := translationProductMap_surjective u b

variable [IsOpenImmersion k.left] [Surjective b.left]

/-- Surjective translation changes detect admissibility of each original invariant coefficient. -/
theorem translationSourceCoefficients_admissible_iff (r : C) :
    translationSourceCoefficients f hL d b c k r ∈
        invariantEnvelopeDenominators f hL d W c' l ↔
      r ∈ invariantEnvelopeDenominators f hL d V c k := by
  refine ⟨?_, translationSourceCoefficients_admissible f hL d b c k r⟩
  intro hr
  rw [mem_invariantEnvelopeDenominators] at hr ⊢
  let g := (prod.map u b).left
  let _ : Surjective g := translationSourceEnvelope_surjective f d b k
  intro y hy
  obtain ⟨z, hz⟩ := g.surjective y
  have hp : g ≫ (prod.fst : prod A V ⟶ A).left =
      (prod.fst : prod (translationSource f d b k) W ⟶ _).left ≫ (u).left :=
    congrArg Over.Hom.left (prod.map_fst u b)
  have H : z ∈ (prod.fst : prod (translationSource f d b k) W ⟶ _).left ⁻¹ᵁ
      (translationSource f d b k).left.basicOpen
        (translationSourceCoefficients f hL d b c k r).val := by
    rw [translationSourceCoefficients_basicOpen]
    change ((prod.fst : prod (translationSource f d b k) W ⟶ _).left ≫ (u).left) z ∈
      A.left.basicOpen r.val
    rw [← hp]
    change (prod.fst : prod A V ⟶ A).left (g z) ∈ A.left.basicOpen r.val
    rw [hz]
    exact hy
  obtain ⟨a, ha⟩ := hr H
  refine ⟨(translationSourceRelationMap f hL d b c k).left a, ?_⟩
  have hs := congrArg Over.Hom.left (translationSourceEnvelope_square f hL d b c k)
  change ((translationSourceRelationMap f hL d b c k).left ≫
    (toEnvelope f hL d V c k).left) a = y
  simp only [Over.comp_left] at hs
  rw [hs]
  change g ((toEnvelope f hL d W c' l).left a) = y
  rw [ha, hz]

/-- The actual original denominator ideal is the inverse image of the refined one. -/
theorem translationSourceDenominators_comap :
    Ideal.comap (translationSourceCoefficients f hL d b c k)
        (invariantEnvelopeDenominators f hL d W c' l) =
      invariantEnvelopeDenominators f hL d V c k := by
  ext r
  exact translationSourceCoefficients_admissible_iff f hL d b c k r

/-- A surjective translation refinement detects whether the entire original envelope is filled. -/
theorem translationSourceEnvelope_isIso_iff :
    IsIso (toEnvelope f hL d W c' l).left ↔ IsIso (toEnvelope f hL d V c k).left := by
  rw [← invariantEnvelopeDenominators_eq_top_iff f hL d W c' l,
    ← invariantEnvelopeDenominators_eq_top_iff f hL d V c k,
    Ideal.eq_top_iff_one, Ideal.eq_top_iff_one]
  simpa only [map_one] using
    translationSourceCoefficients_admissible_iff f hL d b c k (1 : C)

end FLT.Mazur.HilbertChart.AffineRestriction
