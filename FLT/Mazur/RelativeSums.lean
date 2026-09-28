/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RelativeCartierBaseChange
public import FLT.Mazur.SmoothSectionCartier

/-!
# Sums of relative effective Cartier divisors

The product quotient is an extension of the two individual quotients, hence flat.
This proves Stacks 0B8U on common Cartier charts. Finite products retain repeated
sections with their multiplicities and commute with arbitrary base change.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct

universe u

set_option backward.isDefEq.respectTransparency false

namespace FLT.Mazur.FCurve

/-- An extension of flat modules is flat. -/
lemma flat_of_shortExact {R M N P : Type u} [CommRing R]
    [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
    [Module R M] [Module R N] [Module R P]
    [Module.Flat R M] [Module.Flat R P]
    (i : M →ₗ[R] N) (q : N →ₗ[R] P)
    (hi : Function.Injective i) (hq : Function.Surjective q) (he : Function.Exact i q) :
    Module.Flat R N := by
  apply Module.Flat.iff_rTensor_preserves_injective_linearMap.mpr
  intro A B _ _ _ _ f hf
  apply LinearMap.ker_eq_bot.mp
  apply bot_unique
  intro x hx
  change x = 0
  have hx0 : f.rTensor N x = 0 := hx
  have hqx : q.lTensor A x = 0 := by
    apply Module.Flat.rTensor_preserves_injective_linearMap f hf (M := P)
    simpa only [map_zero, ← LinearMap.comp_apply, LinearMap.rTensor_comp_lTensor,
      LinearMap.lTensor_comp_rTensor] using congrArg (q.lTensor B) hx0
  obtain ⟨y, hy⟩ := (lTensor_exact A he hq x).mp hqx
  have hy0 : f.rTensor M y = 0 := by
    apply LinearMap.lTensor_injective_of_exact_of_flat q hq i hi he B
    rw [← LinearMap.comp_apply, LinearMap.lTensor_comp_rTensor,
      ← LinearMap.rTensor_comp_lTensor, LinearMap.comp_apply, hy, map_zero]
    exact hx0
  have : y = 0 := by
    apply Module.Flat.rTensor_preserves_injective_linearMap f hf (M := M)
    simpa only [map_zero] using hy0
  simpa only [this, map_zero] using hy.symm

/-- Flat principal quotients give a flat quotient by the product equation. -/
theorem flat_quotient_mul {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    (a b : B) (hb : IsRegular b)
    [Module.Flat A (B ⧸ Ideal.span {a})] [Module.Flat A (B ⧸ Ideal.span {b})] :
    Module.Flat A (B ⧸ Ideal.span {a * b}) := by
  let i : (B ⧸ Ideal.span {a}) →ₗ[B] B ⧸ Ideal.span {a * b} :=
    Submodule.mapQ _ _ (LinearMap.mul B B b) (by
      intro x hx
      change b * x ∈ Ideal.span {a * b}
      obtain ⟨y, rfl⟩ := Ideal.mem_span_singleton.mp hx
      exact Ideal.mem_span_singleton.mpr ⟨y, by ring⟩)
  have hle : Ideal.span {a * b} ≤ Ideal.span {b} := by
    rw [Ideal.span_singleton_le_iff_mem, Ideal.mem_span_singleton]
    exact ⟨a, mul_comm _ _⟩
  let q := (Ideal.Quotient.factorₐ A hle).toLinearMap
  have hi : Function.Injective i := by
    apply LinearMap.ker_eq_bot.mp
    apply bot_unique
    intro x hx
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    change Ideal.Quotient.mk (Ideal.span {a * b}) (b * x) = 0 at hx
    obtain ⟨y, hy⟩ := Ideal.mem_span_singleton.mp (Ideal.Quotient.eq_zero_iff_mem.mp hx)
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    apply Ideal.mem_span_singleton.mpr
    refine ⟨y, hb.left ?_⟩
    calc b * x = (a * b) * y := hy
         _ = b * (a * y) := by ring
  have hq : Function.Surjective q := Ideal.Quotient.factor_surjective hle
  have he : Function.Exact (i.restrictScalars A) q := by
    intro x
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    change Ideal.Quotient.mk (Ideal.span {b}) x = 0 ↔ _
    rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨Ideal.Quotient.mk (Ideal.span {a}) y, rfl⟩
    · rintro ⟨y, hy⟩
      obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
      have h := congrArg (Ideal.Quotient.factor hle) hy
      change Ideal.Quotient.mk (Ideal.span {b}) (b * y) =
        Ideal.Quotient.mk (Ideal.span {b}) x at h
      have hz : Ideal.Quotient.mk (Ideal.span {b}) (b * y) = 0 :=
        Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton.mpr ⟨y, rfl⟩)
      exact Ideal.mem_span_singleton.mp (Ideal.Quotient.eq_zero_iff_mem.mp (h.symm.trans hz))
  exact flat_of_shortExact (i.restrictScalars A) q hi hq he

variable {X Y S T : Scheme.{u}}

/-- Flatness can be recovered from the quotient maps on local Cartier charts. -/
lemma flat_subscheme_of_chart_quotients (f : X ⟶ S) (I : X.IdealSheafData)
    (H : ∀ x : X, ∃ (V : S.affineOpens) (U : X.affineOpens) (_ : x ∈ U.1)
      (e : U.1 ≤ f ⁻¹ᵁ V.1) (a : Γ(X, U)), I.ideal U = Ideal.span {a} ∧
        ((Ideal.Quotient.mk (Ideal.span {a})).comp (f.appLE V U e).hom).Flat) :
    Flat (I.subschemeι ≫ f) := by
  apply (HasRingHomProperty.iff_exists_appLE (P := @Flat)
    (RingHom.Flat.stableUnderComposition.stableUnderCompositionWithLocalizationAway
      RingHom.Flat.holdsForLocalizationAway).left).mpr
  intro x
  obtain ⟨V, U, hx, e, a, ha, hflat⟩ := H (I.subschemeι x)
  refine ⟨V, ⟨I.subschemeι ⁻¹ᵁ U, U.2.preimage I.subschemeι⟩, hx,
    (fun _ hx ↦ e hx), ?_⟩
  have he := cartierChartQuotientIso_baseMap f I V U e a ha
  change ((f.appLE V U e ≫
    CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {a}))).hom).Flat at hflat
  rw [← he] at hflat
  exact (RingHom.Flat.respectsIso.cancel_right_isIso _
    (cartierChartQuotientIso I U a ha).hom).mp hflat

/-- The sum of two relative effective Cartier divisors is relative effective Cartier. -/
theorem relativeCartierSum (f : X ⟶ S) (I J : X.IdealSheafData) :
    RelativeCartierSum f I J := by
  intro hI hJ
  let := hI.2
  let := hJ.2
  refine ⟨hI.1.mul hJ.1, flat_subscheme_of_chart_quotients f (I * J) ?_⟩
  intro x
  obtain ⟨V, hV, hxV, _⟩ := exists_isAffineOpen_mem_and_subset
    (TopologicalSpace.Opens.mem_top (f x))
  obtain ⟨U₁, hx₁, hUV, hIU⟩ := hI.1.exists_chart_le
    (show x ∈ f ⁻¹ᵁ V from hxV)
  obtain ⟨U, hxU, hU, hJU⟩ := hJ.1.exists_chart_le hx₁
  obtain ⟨a, _, ha⟩ := hIU.mono hU
  obtain ⟨b, hb, hbb⟩ := hJU
  let e : U.1 ≤ f ⁻¹ᵁ V := hU.trans hUV
  let φ := (f.appLE V U e).hom
  let := φ.toAlgebra
  have hqa := flat_cartierChart_quotient f I ⟨V, hV⟩ U e a ha
  have hqb := flat_cartierChart_quotient f J ⟨V, hV⟩ U e b hbb
  have hmap (c : Γ(X, U)) :
      algebraMap Γ(S, V) (Γ(X, U) ⧸ Ideal.span {c}) =
        (Ideal.Quotient.mk (Ideal.span {c})).comp φ := rfl
  let : Module.Flat Γ(S, V) (Γ(X, U) ⧸ Ideal.span {a}) := by
    apply RingHom.flat_algebraMap_iff.mp
    rwa [hmap]
  let : Module.Flat Γ(S, V) (Γ(X, U) ⧸ Ideal.span {b}) := by
    apply RingHom.flat_algebraMap_iff.mp
    rwa [hmap]
  refine ⟨⟨V, hV⟩, U, hxU, e, a * b, ?_, ?_⟩
  · change I.ideal U * J.ideal U = _
    rw [ha, hbb, Ideal.span_singleton_mul_span_singleton]
  · rw [← hmap]
    exact RingHom.flat_algebraMap_iff.mpr (flat_quotient_mul a b hb)

/-- Multiplication notation for relative Cartier sums. -/
lemma RelativeEffectiveCartier.mul {f : X ⟶ S} {I J : X.IdealSheafData}
    (hI : RelativeEffectiveCartier f I) (hJ : RelativeEffectiveCartier f J) :
    RelativeEffectiveCartier f (I * J) := relativeCartierSum f I J hI hJ

/-- The empty divisor is flat over any base. -/
theorem relativeEffectiveCartier_one (f : X ⟶ S) :
    RelativeEffectiveCartier f (1 : X.IdealSheafData) := by
  refine ⟨effectiveCartier_one, ?_⟩
  apply Flat.of_stalkMap
  intro x
  change (⊤ : X.IdealSheafData).subscheme at x
  exact isEmptyElim x

/-- Finite sums of relative Cartier divisors, with the empty sum included. -/
theorem relativeEffectiveCartier_prod {ι : Type*} (f : X ⟶ S)
    (t : Finset ι) (I : ι → X.IdealSheafData)
    (hI : ∀ i ∈ t, RelativeEffectiveCartier f (I i)) :
    RelativeEffectiveCartier f (∏ i ∈ t, I i) := by
  classical
  induction t using Finset.induction_on with
  | empty => simpa using relativeEffectiveCartier_one f
  | @insert i t hi ih =>
    rw [Finset.prod_insert hi]
    exact (hI i (Finset.mem_insert_self i t)).mul
      (ih fun j hj ↦ hI j (Finset.mem_insert_of_mem hj))

/-- Repeated sections are counted with their multiplicity. -/
theorem RelativeEffectiveCartier.pow {f : X ⟶ S} {I : X.IdealSheafData}
    (hI : RelativeEffectiveCartier f I) (n : ℕ) : RelativeEffectiveCartier f (I ^ n) := by
  induction n with
  | zero => simpa using relativeEffectiveCartier_one f
  | succ n hn => simpa only [pow_succ] using hn.mul hI

/-- A finite family of sections of a smooth separated curve defines a relative divisor. -/
theorem relativeEffectiveCartier_section_prod {ι : Type*} (f : X ⟶ S)
    [SmoothOfRelativeDimension 1 f] [IsSeparated f]
    (t : Finset ι) (s : ι → (S ⟶ X)) (hs : ∀ i ∈ t, s i ≫ f = 𝟙 S) :
    RelativeEffectiveCartier f (∏ i ∈ t, (s i).ker) :=
  relativeEffectiveCartier_prod f t _ fun i hi ↦
    smoothSectionCartier f (s i) inferInstance inferInstance (hs i hi)

/-- Pullback of ideal sheaves preserves products for every ambient morphism. -/
theorem idealSheaf_comap_mul (I J : X.IdealSheafData) (k : Y ⟶ X) :
    (I * J).comap k = I.comap k * J.comap k := by
  have H (y : Y) : ∃ (V : X.affineOpens) (U : Y.affineOpens),
      y ∈ U.1 ∧ U.1 ≤ k ⁻¹ᵁ V.1 := by
    obtain ⟨V, hV, hyV, _⟩ := exists_isAffineOpen_mem_and_subset
      (TopologicalSpace.Opens.mem_top (k y))
    obtain ⟨U, hU, hyU, e⟩ := exists_isAffineOpen_mem_and_subset
      (show y ∈ k ⁻¹ᵁ V from hyV)
    exact ⟨⟨V, hV⟩, ⟨U, hU⟩, hyU, e⟩
  choose V U hy e using H
  apply Scheme.IdealSheafData.ext_of_iSup_eq_top U
    (top_unique fun y _ ↦ TopologicalSpace.Opens.mem_iSup.mpr ⟨y, hy y⟩)
  intro y
  simp only [Scheme.IdealSheafData.ideal_mul, Pi.mul_apply]
  rw [Scheme.IdealSheafData.ideal_comap (I * J) k (V y) (U y) (e y),
    Scheme.IdealSheafData.ideal_comap I k (V y) (U y) (e y),
    Scheme.IdealSheafData.ideal_comap J k (V y) (U y) (e y)]
  exact Ideal.map_mul _ _ _

/-- Pullback distributes over finite sums, including the empty sum. -/
theorem idealSheaf_comap_prod {ι : Type*} (t : Finset ι)
    (I : ι → X.IdealSheafData) (k : Y ⟶ X) :
    (∏ i ∈ t, I i).comap k = ∏ i ∈ t, (I i).comap k := by
  classical
  induction t using Finset.induction_on with
  | empty => exact Scheme.IdealSheafData.comap_top k
  | @insert i t hi ih =>
    simp only [Finset.prod_insert hi, idealSheaf_comap_mul, ih]

/-- Finite sums remain relative Cartier after arbitrary base change. -/
theorem relativeEffectiveCartier_prod_baseChange {ι : Type*} (f : X ⟶ S)
    (g : T ⟶ S) (t : Finset ι) (I : ι → X.IdealSheafData)
    (hI : ∀ i ∈ t, RelativeEffectiveCartier f (I i)) :
    RelativeEffectiveCartier (pullback.snd f g)
      (∏ i ∈ t, (I i).comap (pullback.fst f g)) := by
  rw [← idealSheaf_comap_prod]
  exact relativeCartierBaseChange f g _ (relativeEffectiveCartier_prod f t I hI)

/-- Section sums commute with base change as actual ideals, and stay relative Cartier. -/
theorem section_prod_baseChange {ι : Type*} (f : X ⟶ S) (g : T ⟶ S)
    [SmoothOfRelativeDimension 1 f] [IsSeparated f]
    (t : Finset ι) (s : ι → (S ⟶ X)) (hs : ∀ i ∈ t, s i ≫ f = 𝟙 S) :
    (∏ i ∈ t, (s i).ker).comap (pullback.fst f g) =
        ∏ i ∈ t, (s i).ker.comap (pullback.fst f g) ∧
      RelativeEffectiveCartier (pullback.snd f g)
        ((∏ i ∈ t, (s i).ker).comap (pullback.fst f g)) :=
  ⟨idealSheaf_comap_prod t _ _, relativeCartierBaseChange f g _
    (relativeEffectiveCartier_section_prod f t s hs)⟩

/-- The section on the base-changed curve, retaining the equation over its base. -/
def sectionBaseChange (f : X ⟶ S) (g : T ⟶ S) (s : S ⟶ X)
    (hs : s ≫ f = 𝟙 S) : T ⟶ pullback f g :=
  pullback.lift (g ≫ s) (𝟙 T) (by simp [hs])

@[reassoc (attr := simp)]
lemma sectionBaseChange_snd (f : X ⟶ S) (g : T ⟶ S) (s : S ⟶ X)
    (hs : s ≫ f = 𝟙 S) : sectionBaseChange f g s hs ≫ pullback.snd f g = 𝟙 T := by
  simp [sectionBaseChange]

/-- The ideal of the base-changed section is the pullback of the original section ideal. -/
theorem ker_sectionBaseChange (f : X ⟶ S) (g : T ⟶ S) (s : S ⟶ X)
    [IsSeparated f] (hs : s ≫ f = 𝟙 S) :
    (sectionBaseChange f g s hs).ker = s.ker.comap (pullback.fst f g) := by
  let := isClosedImmersion_section f s hs
  have H : IsPullback (sectionBaseChange f g s hs ≫ pullback.snd f g)
      g g (s ≫ f) := by
    simp only [sectionBaseChange_snd, hs]
    exact IsPullback.of_horiz_isIso ⟨by simp⟩
  have K : IsPullback (sectionBaseChange f g s hs) g (pullback.fst f g) s :=
    H.of_right (by simp [sectionBaseChange]) (IsPullback.of_hasPullback f g).flip
  rw [← Scheme.IdealSheafData.ker_fst_of_isClosedImmersion,
    ← Scheme.Hom.ker_comp_of_isIso K.isoPullback.hom, K.isoPullback_hom_fst]

/-- Pullback of a finite section sum is the sum of the base-changed sections themselves. -/
theorem section_prod_comap_eq {ι : Type*} (f : X ⟶ S) (g : T ⟶ S)
    [IsSeparated f] (t : Finset ι) (s : ι → (S ⟶ X))
    (hs : ∀ i, s i ≫ f = 𝟙 S) :
    (∏ i ∈ t, (s i).ker).comap (pullback.fst f g) =
      ∏ i ∈ t, (sectionBaseChange f g (s i) (hs i)).ker := by
  simp only [idealSheaf_comap_prod, ker_sectionBaseChange]

end FLT.Mazur.FCurve
