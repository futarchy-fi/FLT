/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineHilbertFiniteSelectorKernel
public import Mathlib.AlgebraicGeometry.Morphisms.FlatMono

/-!
# A constructed monic finite-model seed meeting every original orbit

The fixed representative scheme is an actual open seed in the original source.
Its coefficient morphism is monic, as proved from finite equations. Original
arrows supply orbit coverage of the entire source. Flatness of the coefficient
morphism is not inferred from the etaleness of the source inclusion.
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
  {A : Over (Spec (.of R))} [IsAffine A.left]
  (k : A ⟶ variableHilbertTest f d V) [IsOpenImmersion k.left]
local notation "p" => fst f hL d V c k
local notation "q" => snd f hL d V c k
local notation "v" => finiteKernelProjection f hL d V c k
local notation "i" => selectorInclusion f hL d V c k
local notation "g" => selectorProjection f hL d V c k

/-- Finite coefficients distinguish the fixed representatives on all relative scheme tests. -/
theorem finiteSelectorFixed_relative_mono
    (r : A.left ⟶ (relation f hL d V c k).left)
    (hr : r ≫ (p).left = 𝟙 A.left)
    (hi : (p).left ≫ r ≫ (q).left = (q).left ≫ r ≫ (q).left) : Mono (i r ≫ v) := by
  constructor
  intro T a b hab
  have hh := finiteKernel_eq_selector f hL d V c k r hr hi (a ≫ i r) (b ≫ i r)
    (by simpa only [Category.assoc] using hab)
  simpa only [Category.assoc, selectorInclusion_projection, Category.comp_id] using hh

/-- The fixed seed retains its monicity after forgetting the original ground. -/
theorem finiteSelectorFixed_mono
    (r : A.left ⟶ (relation f hL d V c k).left)
    (hr : r ≫ (p).left = 𝟙 A.left)
    (hi : (p).left ≫ r ≫ (q).left = (q).left ≫ r ≫ (q).left) : Mono ((i r).left ≫ (v).left) := by
  let _ := finiteSelectorFixed_relative_mono f hL d V c k r hr hi
  exact inferInstanceAs (Mono (i r ≫ v).left)

omit [IsAffine A.left] in
/-- The representative inclusion is an actual open seed, proved from its etale retraction. -/
theorem finiteSelectorFixed_isOpenImmersion
    (r : A.left ⟶ (relation f hL d V c k).left)
    (hr : r ≫ (p).left = 𝟙 A.left)
    (hi : (p).left ≫ r ≫ (q).left = (q).left ≫ r ≫ (q).left) : IsOpenImmersion (i r).left := by
  obtain ⟨he, _⟩ := selectorProjection_cover f hL d V c k r hr hi
  let _ := he
  have hh : (i r).left ≫ (g r hr hi).left = 𝟙 _ :=
    congrArg Over.Hom.left (selectorInclusion_projection f hL d V c k r hr hi)
  let _ : Etale ((i r).left ≫ (g r hr hi).left) := by rw [hh]; infer_instance
  let _ : Etale (i r).left := Etale.of_comp (i r).left (g r hr hi).left
  let _ : Mono (i r).left :=
    inferInstanceAs (Mono (SchemeRelationSelectorQuotient.inclusion («q» := q) r))
  exact IsOpenImmersion.of_flat_of_mono (i r).left

omit [Etale V.hom] [IsAffine A.left] [IsOpenImmersion k.left] in
/-- Every original source orbit has a constructed point on this single fixed seed. -/
theorem finiteSelectorFixed_orbits
    (r : A.left ⟶ (relation f hL d V c k).left)
    (hr : r ≫ (p).left = 𝟙 A.left)
    (hi : (p).left ≫ r ≫ (q).left = (q).left ≫ r ≫ (q).left) (x : A.left) :
    ∃ z : (selectorTarget f hL d V c k r).left,
      RelativeRelationOrbit.Related p q x ((i r).left z) :=
  ⟨(g r hr hi).left x, selector_representative_related f hL d V c k r hr hi x⟩

/-- The original finite projection factors through the fixed seed with its exact coefficients. -/
@[reassoc]
theorem finiteSelectorFixed_factor
    (r : A.left ⟶ (relation f hL d V c k).left)
    (hr : r ≫ (p).left = 𝟙 A.left)
    (hi : (p).left ≫ r ≫ (q).left = (q).left ≫ r ≫ (q).left) : g r hr hi ≫ (i r ≫ v) = v := by
  apply Over.OverMorphism.ext
  exact SchemeRelationSelectorQuotient.projection_descend r hr hi (v).left
    (congrArg Over.Hom.left (finiteKernelProjection_condition f hL d V c k))

end FLT.Mazur.HilbertChart.AffineRestriction
