/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.OneGonLocalFactorization
public import FLT.Mazur.OneGonMapGluing

/-!
# Descent and gluing on a refined cover of the pinched chart

An endpoint-compatible map to an arbitrary scheme descends near the node
using an affine target factorization. We glue it with the puncture map.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Polynomial
open FLT.Mazur.PolygonNodePresentation FLT.Mazur.OneGonPinchingAlgebra
open FLT.Mazur.OneGonLocalizedPinching FLT.Mazur.OneGonLocalFactorization
open FLT.Mazur.OneGonMapGluing

namespace FLT.Mazur.OneGonRefinedDescent

universe u

/-- A two-member open cover specified by its covering property. -/
def twoCover {W Y Z : Scheme.{u}} (i : Y ⟶ W) (j : Z ⟶ W)
    [IsOpenImmersion i] [IsOpenImmersion j]
    (hc : ∀ x : W, x ∈ Set.range i ∨ x ∈ Set.range j) : W.OpenCover :=
  Scheme.Cover.mkOfCovers Bool (Bool.rec Z Y) (Bool.rec j i)
    (by
      intro x
      rcases hc x with ⟨y, hy⟩ | ⟨z, hz⟩
      · exact ⟨true, y, hy⟩
      · exact ⟨false, z, hz⟩)
    (by intro b; cases b <;> infer_instance)

/-- Glue two maps after proving their equality on the actual intersection. -/
theorem exists_glue_two {W Y Z T : Scheme.{u}} (i : Y ⟶ W) (j : Z ⟶ W)
    [IsOpenImmersion i] [IsOpenImmersion j]
    (hc : ∀ x : W, x ∈ Set.range i ∨ x ∈ Set.range j)
    (f : Y ⟶ T) (g : Z ⟶ T)
    (h : pullback.fst i j ≫ f = pullback.snd i j ≫ g) :
    ∃ d : W ⟶ T, i ≫ d = f ∧ j ≫ d = g := by
  let c := twoCover i j hc
  let m : ∀ b, c.X b ⟶ T := Bool.rec g f
  have hm : ∀ b b', pullback.fst (c.f b) (c.f b') ≫ m b =
      pullback.snd _ _ ≫ m b' := by
    intro b b'
    cases b <;> cases b'
    · change pullback.fst j j ≫ g = pullback.snd j j ≫ g
      rw [show pullback.fst j j = pullback.snd j j from
        (cancel_mono j).mp pullback.condition]
    · change pullback.fst j i ≫ g = pullback.snd j i ≫ f
      apply (cancel_epi (pullbackSymmetry i j).hom).mp
      simpa only [← Category.assoc, pullbackSymmetry_hom_comp_fst,
        pullbackSymmetry_hom_comp_snd] using h.symm
    · exact h
    · change pullback.fst i i ≫ f = pullback.snd i i ≫ f
      rw [show pullback.fst i i = pullback.snd i i from
        (cancel_mono i).mp pullback.condition]
  exact ⟨c.glueMorphisms m hm, c.ι_glueMorphisms m hm true,
    c.ι_glueMorphisms m hm false⟩

/-- Equality of maps can be checked on either member of a two-member open cover. -/
theorem hom_ext_two {W Y Z T : Scheme.{u}} (i : Y ⟶ W) (j : Z ⟶ W)
    [IsOpenImmersion i] [IsOpenImmersion j]
    (hc : ∀ x : W, x ∈ Set.range i ∨ x ∈ Set.range j)
    (f g : W ⟶ T) (hi : i ≫ f = i ≫ g) (hj : j ≫ f = j ≫ g) : f = g := by
  apply (twoCover i j hc).hom_ext
  intro b
  cases b
  · exact hj
  · exact hi

variable {K : Type u} [Field K]

/-- Inclusion of the chosen principal neighborhood in the pinched chart. -/
def chartInclusion (s : B (R := K)) :
    Spec (.of (chart s)) ⟶ Spec (.of (B (R := K))) :=
  Spec.map (CommRingCat.ofHom (algebraMap (B (R := K)) (chart s)))

instance (s : B (R := K)) : IsOpenImmersion (chartInclusion s) := by
  unfold chartInclusion
  infer_instance

instance (s : B (R := K)) : IsOpenImmersion (lineInclusion s) := by
  unfold lineInclusion
  infer_instance

instance : IsOpenImmersion (punctureToLine (K := K)) := by
  unfold punctureToLine
  infer_instance

@[reassoc]
theorem normalization_square (s : B (R := K)) :
    Spec.map (CommRingCat.ofHom (restriction s)) ≫ chartInclusion s =
      lineInclusion s ≫ toPinching := by
  rw [chartInclusion, lineInclusion, toPinching, ← Spec.map_comp, ← Spec.map_comp]
  apply congrArg Spec.map
  apply ConcreteCategory.hom_ext
  intro b
  exact restriction_algebraMap s b

/-- Localizing the normalization is the pullback of the principal node chart. -/
theorem normalization_isPullback (s : B (R := K)) :
    IsPullback (Spec.map (CommRingCat.ofHom (restriction s)))
      (lineInclusion s) (chartInclusion s) toPinching := by
  apply IsOpenImmersion.isPullback _ _ _ _ (normalization_square s).symm
  have h₁ : (chartInclusion s).opensRange = PrimeSpectrum.basicOpen s :=
    TopologicalSpace.Opens.ext (PrimeSpectrum.localization_away_comap_range (chart s) s)
  have h₂ : (lineInclusion s).opensRange = PrimeSpectrum.basicOpen s.val :=
    TopologicalSpace.Opens.ext (range_lineInclusion s)
  rw [h₁, h₂]
  rfl

/-- Descent on a principal node neighborhood for any affine target scheme. -/
theorem exists_local_desc {T : Scheme.{u}} [IsAffine T]
    (s : B (R := K)) (hs : bEval s ≠ 0)
    (k : Spec (.of (line s)) ⟶ T)
    (hk : Spec.map (CommRingCat.ofHom (atZero s hs)) ≫ k =
      Spec.map (CommRingCat.ofHom (atOne s hs)) ≫ k) :
    ∃ d : Spec (.of (chart s)) ⟶ T,
      Spec.map (CommRingCat.ofHom (restriction s)) ≫ d = k := by
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (k ≫ T.isoSpec.hom)
  have he : (atZero s hs).comp φ.hom = (atOne s hs).comp φ.hom := by
    have h := congrArg (fun m ↦ m ≫ T.isoSpec.hom) hk
    rw [Category.assoc, Category.assoc, ← hφ, ← Spec.map_comp, ← Spec.map_comp] at h
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective h)
  refine ⟨OneGonLocalMaps.localMap s hs φ.hom he ≫ T.isoSpec.inv, ?_⟩
  rw [← Category.assoc, OneGonLocalMaps.normalization_localMap]
  change Spec.map φ ≫ T.isoSpec.inv = k
  rw [hφ]
  simp


/-- The chosen principal neighborhood and puncture cover the pinched chart. -/
theorem chart_cover (s : B (R := K)) (hs : bEval s ≠ 0)
    (p : Spec (.of (B (R := K)))) :
    p ∈ Set.range (chartInclusion s) ∨ p ∈ Set.range (bPuncture K) := by
  rcases OneGonNodeFiber.principal_puncture_cover s hs p with hp | hp
  · left
    exact (Set.ext_iff.mp (PrimeSpectrum.localization_away_comap_range (chart s) s) p).mpr hp
  · right
    exact (Set.ext_iff.mp (range_bPuncture K) p).mpr hp

/-- The corresponding two open charts also cover the affine normalization. -/
theorem line_cover (s : B (R := K)) (hs : bEval s ≠ 0)
    (p : Spec (.of K[X])) :
    p ∈ Set.range (lineInclusion s) ∨ p ∈ Set.range (punctureToLine (K := K)) := by
  rcases OneGonNodeFiber.principal_puncture_cover s hs (toPinching p) with hp | hp
  · left
    exact (Set.ext_iff.mp (range_lineInclusion s) p).mpr hp
  · right
    exact (Set.ext_iff.mp (PrimeSpectrum.localization_away_comap_range
      (OneGonTransition.puncture K) (Polynomial.X * (Polynomial.X - 1))) p).mpr hp

/-- A descended principal map and the original puncture map agree on their intersection. -/
theorem overlap_compatible {T : Scheme.{u}} (s : B (R := K))
    (f : Spec (.of K[X]) ⟶ T) (d : Spec (.of (chart s)) ⟶ T)
    (hd : Spec.map (CommRingCat.ofHom (restriction s)) ≫ d = lineInclusion s ≫ f) :
    pullback.fst (chartInclusion s) (bPuncture K) ≫ d =
      pullback.snd (chartInclusion s) (bPuncture K) ≫ punctureToLine ≫ f := by
  have hw : pullback.fst (chartInclusion s) (bPuncture K) ≫ chartInclusion s =
      (pullback.snd (chartInclusion s) (bPuncture K) ≫ punctureToLine) ≫ toPinching := by
    rw [Category.assoc, puncture_toPinching]
    exact pullback.condition
  let a := (normalization_isPullback s).lift
    (pullback.fst (chartInclusion s) (bPuncture K))
    (pullback.snd (chartInclusion s) (bPuncture K) ≫ punctureToLine) hw
  have h₁ : a ≫ Spec.map (CommRingCat.ofHom (restriction s)) =
      pullback.fst (chartInclusion s) (bPuncture K) := IsPullback.lift_fst _ _ _ _
  have h₂ : a ≫ lineInclusion s =
      pullback.snd (chartInclusion s) (bPuncture K) ≫ punctureToLine :=
    IsPullback.lift_snd _ _ _ _
  rw [← h₁, Category.assoc, hd, ← Category.assoc, h₂, Category.assoc]

/-- Glue the local descent with the puncture map and recover the entire normalization map. -/
theorem exists_desc_of_local {T : Scheme.{u}} (s : B (R := K)) (hs : bEval s ≠ 0)
    (f : Spec (.of K[X]) ⟶ T) (d : Spec (.of (chart s)) ⟶ T)
    (hd : Spec.map (CommRingCat.ofHom (restriction s)) ≫ d = lineInclusion s ≫ f) :
    ∃ g : Spec (.of (B (R := K))) ⟶ T,
      toPinching ≫ g = f ∧ chartInclusion s ≫ g = d ∧
        bPuncture K ≫ g = punctureToLine ≫ f := by
  obtain ⟨g, hg₁, hg₂⟩ := exists_glue_two (chartInclusion s) (bPuncture K)
    (chart_cover s hs) d (punctureToLine ≫ f) (overlap_compatible s f d hd)
  refine ⟨g, ?_, hg₁, hg₂⟩
  apply hom_ext_two (lineInclusion s) punctureToLine (line_cover s hs)
  · rw [← Category.assoc, ← normalization_square, Category.assoc, hg₁, hd]
  · rw [← Category.assoc, puncture_toPinching, hg₂]

/-- Every endpoint-compatible morphism to an arbitrary scheme descends uniquely. -/
theorem existsUnique_desc {T : Scheme.{u}}
    (f : Spec (.of K[X]) ⟶ T)
    (hf : endpointSection 0 ≫ f = endpointSection 1 ≫ f) :
    ∃! g : Spec (.of (B (R := K))) ⟶ T, toPinching ≫ g = f := by
  obtain ⟨s, hs, U, hU, k, hk, he⟩ := exists_compatible_node_factorization f hf
  let : IsAffine (U : Scheme) := hU
  obtain ⟨d, hd⟩ := exists_local_desc s hs k he
  have hd' : Spec.map (CommRingCat.ofHom (restriction s)) ≫ (d ≫ U.ι) =
      lineInclusion s ≫ f := by
    rw [← Category.assoc, hd, hk]
  obtain ⟨g, hg, _⟩ := exists_desc_of_local s hs f (d ≫ U.ι) hd'
  exact ⟨g, hg, fun g' hg' ↦ OneGonDescentUniqueness.hom_ext g' g (hg'.trans hg.symm)⟩


/-- The uniquely descended map on the entire pinched affine chart. -/
def desc {T : Scheme.{u}} (f : Spec (.of K[X]) ⟶ T)
    (hf : endpointSection 0 ≫ f = endpointSection 1 ≫ f) :
    Spec (.of (B (R := K))) ⟶ T :=
  (existsUnique_desc f hf).choose

@[reassoc (attr := simp)]
theorem normalization_desc {T : Scheme.{u}} (f : Spec (.of K[X]) ⟶ T)
    (hf : endpointSection 0 ≫ f = endpointSection 1 ≫ f) :
    toPinching ≫ desc f hf = f :=
  (existsUnique_desc f hf).choose_spec.1


/-- The unique descent restricts to any local descent constructed on the refined cover. -/
theorem principal_desc {T : Scheme.{u}} (s : B (R := K)) (hs : bEval s ≠ 0)
    (f : Spec (.of K[X]) ⟶ T)
    (hf : endpointSection 0 ≫ f = endpointSection 1 ≫ f)
    (d : Spec (.of (chart s)) ⟶ T)
    (hd : Spec.map (CommRingCat.ofHom (restriction s)) ≫ d = lineInclusion s ≫ f) :
    chartInclusion s ≫ desc f hf = d := by
  obtain ⟨g, hg, hchart, _⟩ := exists_desc_of_local s hs f d hd
  have he : g = desc f hf :=
    OneGonDescentUniqueness.hom_ext _ _ (hg.trans (normalization_desc f hf).symm)
  rwa [he] at hchart

open OneGonGluing OneGonTransition

variable {T : Scheme.{u}} (f : Spec (.of K[X]) ⟶ T)
    (hf : endpointSection 0 ≫ f = endpointSection 1 ≫ f)
    (g : torusChart K ⟶ T)
    (h : punctureToLine ≫ f = toTorus K ≫ g)

include h in
/-- The descended node map agrees with the torus map on the prescribed overlap. -/
theorem torus_compatible : bPuncture K ≫ desc f hf = toTorus K ≫ g := by
  rw [← puncture_toPinching, Category.assoc, normalization_desc]
  exact h

/-- Glue an arbitrary endpoint-compatible normalization map to a compatible torus map. -/
def gluedMap : scheme K ⟶ T :=
  pushout.desc (desc f hf) g (torus_compatible f hf g h)

@[reassoc (attr := simp)]
theorem node_gluedMap : node K ≫ gluedMap f hf g h = desc f hf :=
  pushout.inl_desc _ _ _

@[reassoc (attr := simp)]
theorem torus_gluedMap : torus K ≫ gluedMap f hf g h = g :=
  pushout.inr_desc _ _ _

/-- The global map recovers the original map on the affine normalization. -/
theorem normalization_gluedMap :
    toPinching ≫ node K ≫ gluedMap f hf g h = f := by
  rw [node_gluedMap, normalization_desc]

/-- The two original maps uniquely determine the glued morphism. -/
theorem gluedMap_unique (d : scheme K ⟶ T)
    (hd : toPinching ≫ node K ≫ d = f) (hg : torus K ≫ d = g) :
    d = gluedMap f hf g h := by
  apply pushout.hom_ext
  · change node K ≫ d = node K ≫ gluedMap f hf g h
    rw [node_gluedMap]
    exact OneGonDescentUniqueness.hom_ext _ _ (hd.trans (normalization_desc f hf).symm)
  · exact hg.trans (torus_gluedMap f hf g h).symm

end FLT.Mazur.OneGonRefinedDescent
