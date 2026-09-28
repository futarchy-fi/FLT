/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FamilyTransport

/-!
# Finite locally free morphisms of constant degree

Constant degree uses the rank of the finite flat algebra, including multiplicities.
It is preserved by arbitrary base change and by isomorphisms over the base.
The pullback convention agrees with `familyPullback`: the structure map is the
second projection. All results allow disconnected and empty bases.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace FLT.Mazur.FCurve

variable {D S T : Scheme.{u}} {n : ℕ}

/-- Finiteness is invariant under an isomorphism over the base. -/
theorem isFinite_iff_of_overIso {X Y : Over S} (e : X ≅ Y) :
    IsFinite X.hom ↔ IsFinite Y.hom := by
  constructor
  · intro hX
    let := hX
    rw [← Over.w e.inv]
    infer_instance
  · intro hY
    let := hY
    rw [← Over.w e.hom]
    infer_instance

/-- An over-isomorphism preserves the entire rank function. -/
theorem finrank_eq_of_overIso {X Y : Over S} (e : X ≅ Y)
    [IsFinite Y.hom] [Flat Y.hom] : X.hom.finrank = Y.hom.finrank := by
  rw [← Over.w e.hom, Scheme.Hom.finrank_comp_left_of_isIso]

/-- Constant degree is invariant under isomorphisms retaining the structure map. -/
theorem finiteLocallyFreeDegree_iff_of_overIso {X Y : Over S} (e : X ≅ Y) :
    FiniteLocallyFreeDegree X.hom n ↔ FiniteLocallyFreeDegree Y.hom n := by
  have transport {X Y : Over S} (e : X ≅ Y)
      (h : FiniteLocallyFreeDegree Y.hom n) : FiniteLocallyFreeDegree X.hom n := by
    obtain ⟨hi, hf, hl, hn⟩ := h
    let := hi
    let := hf
    refine ⟨(isFinite_iff_of_overIso e).mpr hi, (flat_iff_of_overIso e).mpr hf,
      (locallyOfFinitePresentation_iff_of_overIso e).mpr hl, ?_⟩
    simpa only [finrank_eq_of_overIso e] using hn
  exact ⟨transport e.symm, transport e⟩

/-- Arbitrary base change preserves all four parts of the degree contract. -/
theorem degreeBaseChange (f : D ⟶ S) (g : T ⟶ S) (n : ℕ) :
    DegreeBaseChange f g n := by
  intro ⟨hi, hf, hl, hn⟩
  let := hi
  let := hf
  let := hl
  refine ⟨inferInstance, inferInstance, inferInstance, fun t ↦ ?_⟩
  rw [Scheme.Hom.finrank_pullback_snd, hn]

namespace FiniteLocallyFreeDegree

/-- Method form of arbitrary base change for later subgroup records. -/
theorem baseChange {f : D ⟶ S} (hf : FiniteLocallyFreeDegree f n) (g : T ⟶ S) :
    FiniteLocallyFreeDegree (pullback.snd f g) n :=
  degreeBaseChange f g n hf

/-- Transport constant degree along an isomorphism over the base. -/
theorem of_overIso {X Y : Over S} (hX : FiniteLocallyFreeDegree X.hom n) (e : X ≅ Y) :
    FiniteLocallyFreeDegree Y.hom n :=
  (finiteLocallyFreeDegree_iff_of_overIso e).mp hX

/-- Positive constant degree forces surjectivity onto the base. -/
theorem surjective {f : D ⟶ S} (hf : FiniteLocallyFreeDegree f n) (hn : 0 < n) :
    Surjective f := by
  obtain ⟨hi, hflat, _, hrank⟩ := hf
  let := hi
  let := hflat
  apply (Scheme.Hom.one_le_finrank_iff_surjective f).mp
  intro s
  change 1 ≤ f.finrank s
  rw [hrank]
  exact hn

/-- A finite locally free morphism of degree one is an isomorphism. -/
theorem isIso {f : D ⟶ S} (hf : FiniteLocallyFreeDegree f 1) : IsIso f := by
  obtain ⟨hi, hflat, _, hrank⟩ := hf
  let := hi
  let := hflat
  exact (Scheme.Hom.isIso_iff_finrank_eq f).mpr (funext hrank)

end FiniteLocallyFreeDegree

/-- Isomorphisms have degree one, including over an empty base. -/
theorem finiteLocallyFreeDegree_one_of_isIso (f : D ⟶ S) [IsIso f] :
    FiniteLocallyFreeDegree f 1 := by
  refine ⟨inferInstance, inferInstance, inferInstance, fun s ↦ ?_⟩
  exact congrFun (Scheme.Hom.finrank_eq_one_of_isIso f) s

/-- Degree one characterizes isomorphisms without extra hypotheses. -/
theorem finiteLocallyFreeDegree_one_iff (f : D ⟶ S) :
    FiniteLocallyFreeDegree f 1 ↔ IsIso f :=
  ⟨fun h ↦ h.isIso, fun _ ↦ finiteLocallyFreeDegree_one_of_isIso f⟩

/-- Constant degree on the FC01 pullback object. -/
theorem finiteLocallyFreeDegree_familyPullback {X : Over S}
    (hX : FiniteLocallyFreeDegree X.hom n) (g : T ⟶ S) :
    FiniteLocallyFreeDegree (familyPullback X g).hom n :=
  hX.baseChange g

/-- The identity comparison retains the degree condition in both directions. -/
theorem finiteLocallyFreeDegree_familyPullback_id_iff (X : Over S) :
    FiniteLocallyFreeDegree (familyPullback X (𝟙 S)).hom n ↔
      FiniteLocallyFreeDegree X.hom n :=
  finiteLocallyFreeDegree_iff_of_overIso (familyPullbackIdIso X)

/-- The composite comparison retains the degree condition over the final base. -/
theorem finiteLocallyFreeDegree_familyPullback_comp_iff {U : Scheme.{u}}
    (X : Over S) (g : T ⟶ S) (h : U ⟶ T) :
    FiniteLocallyFreeDegree (familyPullback (familyPullback X g) h).hom n ↔
      FiniteLocallyFreeDegree (familyPullback X (h ≫ g)).hom n :=
  finiteLocallyFreeDegree_iff_of_overIso (familyPullbackCompIso X g h)

section Affine

variable (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]
  [Module.Finite R A] [Module.Flat R A]

/-- On affine schemes, degree is the local module rank of the defining algebra. -/
theorem finrank_spec_algebraMap (s : PrimeSpectrum R) :
    (Spec.map (CommRingCat.ofHom (algebraMap R A))).finrank s =
      Module.rankAtStalk A s :=
  Scheme.Hom.finrank_SpecMap_algebraMap R A s

/-- The affine criterion includes algebra finite presentation explicitly. -/
theorem finiteLocallyFreeDegree_spec_algebraMap_iff [Algebra.FinitePresentation R A] :
    FiniteLocallyFreeDegree (Spec.map (CommRingCat.ofHom (algebraMap R A))) n ↔
      ∀ s : PrimeSpectrum R, Module.rankAtStalk A s = n := by
  have hi : IsFinite (Spec.map (CommRingCat.ofHom (algebraMap R A))) := by
    rw [IsFinite.SpecMap_iff]
    exact RingHom.finite_algebraMap.mpr inferInstance
  have hf : Flat (Spec.map (CommRingCat.ofHom (algebraMap R A))) := by
    rw [Flat.SpecMap_iff]
    exact RingHom.flat_algebraMap_iff.mpr inferInstance
  have hl : LocallyOfFinitePresentation
      (Spec.map (CommRingCat.ofHom (algebraMap R A))) := by
    rw [LocallyOfFinitePresentation.SpecMap_iff]
    exact RingHom.finitePresentation_algebraMap.mpr inferInstance
  simp only [FiniteLocallyFreeDegree, hi, hf, hl, true_and]
  change (∀ s : PrimeSpectrum R,
    (Spec.map (CommRingCat.ofHom (algebraMap R A))).finrank s = n) ↔ _
  simp only [finrank_spec_algebraMap]

end Affine

end FLT.Mazur.FCurve
