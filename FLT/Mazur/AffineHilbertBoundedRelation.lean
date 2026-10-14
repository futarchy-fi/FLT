/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineHilbertDerivedNoetherianRelation

/-!
# Noetherianity of the full relation for arbitrary étale translations

The original relation embeds in its envelope, but its image factors through the
Noetherian scheme of pairs of actual selected parameters. The continuous image
of that pair scheme is Noetherian, as is every embedded subspace. Thus the whole
relation is Noetherian even when the translation is neither affine nor compact.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace
namespace FLT.Mazur.HilbertChart.AffineRestriction
open CartierAbel SchemePicard FCurve
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R] {X : Scheme}
  (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  (d : ℕ) (V : Over (Spec (.of R))) [Etale V.hom]
  (c : (relativeFppfSheaf f).obj.obj (op V))
  {A : Over (Spec (.of R))} [IsAffine A.left]
  (k : A ⟶ variableHilbertTest f d V) [IsOpenImmersion k.left]
local notation "p" => fst f hL d V c k
local notation "q" => snd f hL d V c k
local notation "β" => k ≫ variableHilbertBase f d V
local notation "E" => toEnvelope f hL d V c k

include k in
/-- The pair scheme uses the actual selected parameter twice and is Noetherian. -/
theorem selectedParameterPair_isNoetherian : IsNoetherian (prod A A).left := by
  let _ := selectedHilbertSource_isLocallyNoetherian f d V k
  let _ : LocallyOfFiniteType A.hom := by
    rw [← k.w]
    infer_instance
  let _ : LocallyOfFiniteType (prod.fst : prod A A ⟶ A).left := by
    rw [← Over.prodLeftIsoPullback_hom_fst A A]
    infer_instance
  let _ := LocallyOfFiniteType.isLocallyNoetherian (prod.fst : prod A A ⟶ A).left
  let _ := variableHilbertOverlap_envelope_affine A A
  exact ⟨⟩

omit [Etale V.hom] [IsAffine A.left] [IsOpenImmersion k.left] in
/-- Both original endpoints bound the envelope image inside the actual parameter-pair image. -/
@[reassoc]
theorem fullRelation_envelope_factor : prod.lift q p ≫ prod.map (𝟙 A) β = E := by
  apply prod.hom_ext
  · simp only [Category.assoc, prod.map_fst, Category.comp_id, prod.lift_fst,
      toEnvelope_test]
  · simp only [Category.assoc, prod.map_snd, prod.lift_snd_assoc, toEnvelope_base]

/-- The full relation is a Noetherian space for every selected étale translation. -/
theorem fullRelation_bounded_noetherianSpace :
    NoetherianSpace (relation f hL d V c k).left := by
  let _ := selectedParameterPair_isNoetherian f d V k
  let g := (prod.map (𝟙 A) β).left
  let _ : NoetherianSpace (Set.range g) := NoetherianSpace.range g g.continuous
  have hr (x : (relation f hL d V c k).left) : (E).left x ∈ Set.range g := by
    refine ⟨(prod.lift q p).left x, ?_⟩
    exact congrArg (fun z ↦ z.left x) (fullRelation_envelope_factor f hL d V c k)
  exact ((E).left.isOpenEmbedding.isEmbedding.isInducing.codRestrict hr).noetherianSpace

/-- No affine or quasi-compact hypothesis is needed on the translation scheme. -/
instance fullRelation_arbitraryTranslation_isNoetherian :
    IsNoetherian (relation f hL d V c k).left := by
  let _ := selectedHilbertSource_isLocallyNoetherian f d V k
  let _ := envelope_isLocallyNoetherian V (A := A)
  let _ := isLocallyNoetherian_of_isOpenImmersion (E).left
  let _ := fullRelation_bounded_noetherianSpace f hL d V c k
  exact ⟨⟩

/-- The first full endpoint is quasi-compact for arbitrary étale translations. -/
instance fullRelation_arbitraryTranslation_fst_quasiCompact : QuasiCompact (p).left := by
  infer_instance

/-- The independent second endpoint is quasi-compact without restricting the translation. -/
instance fullRelation_arbitraryTranslation_snd_quasiCompact : QuasiCompact (q).left := by
  infer_instance

end FLT.Mazur.HilbertChart.AffineRestriction
