/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.DivisorLineBundle

/-!
# Coherence of Cartier chart restrictions

Dual ideal restrictions preserve identities, composition, and the tensor comparison.
Affine ring isomorphisms of open immersions transport these actual chart modules.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct

universe u

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

attribute [local instance] RingHomInvPair.of_ringEquiv RingHomInvPair.of_ringEquiv_symm

namespace FLT.Mazur.FCurve
namespace CartierModule

variable {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]

lemma dualRestrict_id (I : Ideal R) (a : R) (ha : IsRegular a)
    (hI : I = Ideal.span {a}) :
    dualRestrict (RingHom.id R) I I a ha ha hI hI = LinearMap.id := by
  symm
  apply dualRestrict_unique _ _ _ _ _ _ _ _ (by simp)
  intro f x
  rfl

lemma dualRestrict_comp (σ : R →+* S) (τ : S →+* T)
    (I : Ideal R) (J : Ideal S) (K : Ideal T) (a : R)
    (ha : IsRegular a) (hσa : IsRegular (σ a)) (hτa : IsRegular (τ (σ a)))
    (hI : I = Ideal.span {a}) (hJ : J = Ideal.span {σ a})
    (hK : K = Ideal.span {τ (σ a)}) (f : Dual I) :
    dualRestrict τ J K (σ a) hσa hτa hJ hK
      (dualRestrict σ I J a ha hσa hI hJ f) =
        dualRestrict (τ.comp σ) I K a ha hτa hI hK f := by
  let : RingHomCompTriple σ τ (τ.comp σ) := ⟨rfl⟩
  have hIJ : I.map σ ≤ J := by
    rw [hI, hJ, Ideal.map_span, Set.image_singleton]
  have hJK : J.map τ ≤ K := by
    rw [hJ, hK, Ideal.map_span, Set.image_singleton]
  have hIK : I.map (τ.comp σ) ≤ K := by
    rw [hI, hK, Ideal.map_span, Set.image_singleton]
    rfl
  suffices he : (dualRestrict τ J K (σ a) hσa hτa hJ hK).comp
      (dualRestrict σ I J a ha hσa hI hJ) =
        dualRestrict (τ.comp σ) I K a ha hτa hI hK from congrArg (fun F ↦ F f) he
  apply dualRestrict_unique _ _ _ _ _ _ _ _ hIK
  intro g x
  change dualRestrict τ J K (σ a) hσa hτa hJ hK
    (dualRestrict σ I J a ha hσa hI hJ g)
      (idealRestrict τ J K hJK (idealRestrict σ I J hIJ x)) = _
  rw [dualRestrict_apply, dualRestrict_apply]
  rfl

/-- A ring isomorphism transports the actual ideals semilinearly. -/
def idealTransport (e : R ≃+* S) (I : Ideal R) (J : Ideal S) (h : I.map e = J) :
    I ≃ₛₗ[(e : R →+* S)] J :=
  LinearEquiv.ofBijective (idealRestrict (e : R →+* S) I J h.le) ⟨fun x y hxy ↦
    Subtype.ext (e.injective (congrArg Subtype.val hxy)), fun y ↦ by
      obtain ⟨x, hx, hxy⟩ := (Ideal.mem_map_of_equiv e (y : S)).mp (by rw [h]; exact y.property)
      exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩⟩

/-- Transport of duals uses conjugation by the ideal and ring isomorphisms. -/
def dualTransport (e : R ≃+* S) (I : Ideal R) (J : Ideal S) (h : I.map e = J) :
    Dual I ≃ₛₗ[(e : R →+* S)] Dual J :=
  (idealTransport e I J h).arrowCongr e.toSemilinearEquiv

lemma dualTransport_apply (e : R ≃+* S) (I : Ideal R) (J : Ideal S)
    (h : I.map e = J) (f : Dual I) (x : I) :
    dualTransport e I J h f (idealRestrict (e : R →+* S) I J h.le x) = e (f x) := by
  change e (f ((idealTransport e I J h).symm (idealTransport e I J h x))) = _
  rw [LinearEquiv.symm_apply_apply]

/-- On regular principal ideals, transport is exactly dual restriction. -/
lemma dualTransport_eq_dualRestrict (e : R ≃+* S) (I : Ideal R) (J : Ideal S)
    (h : I.map e = J) (a : R) (ha : IsRegular a) (hea : IsRegular (e a))
    (hI : I = Ideal.span {a}) (hJ : J = Ideal.span {e a}) :
    (dualTransport e I J h).toLinearMap =
      dualRestrict (e : R →+* S) I J a ha hea hI hJ := by
  exact dualRestrict_unique (e : R →+* S) I J a ha hea hI hJ h.le
    (dualTransport e I J h).toLinearMap (dualTransport_apply e I J h)

end CartierModule

variable {X Y : Scheme.{u}}

/-- Evaluation on restricted ideal sections detects equality on a smaller chart. -/
lemma CartierChart.dual_ext_restrict {I : X.IdealSheafData} {U V : X.affineOpens}
    (hV : CartierChart I V) (hUV : U ≤ V) {f g : divisorChartModule I U}
    (he : ∀ x, f (CartierModule.idealRestrict _ _ _ (I.map_ideal hUV).le x) =
      g (CartierModule.idealRestrict _ _ _ (I.map_ideal hUV).le x)) : f = g := by
  apply CartierModule.dual_ext _ _ (regular_restrict hUV hV.choose_spec.1)
    (ideal_eq_span_restrict I hUV hV.choose_spec.2)
  convert he (hV.idealEquiv 1) using 1 <;>
    congr 1 <;> apply Subtype.ext <;> simp [CartierModule.idealRestrict,
      CartierChart.idealEquiv] <;> rfl

lemma CartierChart.dualRestrict_id {I : X.IdealSheafData} {U : X.affineOpens}
    (hU : CartierChart I U) (f : divisorChartModule I U) :
    hU.dualRestrict le_rfl f = f := by
  apply hU.dual_ext_restrict le_rfl
  intro x
  rw [CartierChart.dualRestrict_apply]
  have he : CartierModule.idealRestrict _ _ _ (I.map_ideal le_rfl).le x = x := by
    apply Subtype.ext
    change (X.presheaf.map (𝟙 _)).hom _ = _
    rw [X.presheaf.map_id]
    rfl
  rw [he]
  change (X.presheaf.map (𝟙 _)).hom _ = _
  rw [X.presheaf.map_id]
  rfl

lemma CartierChart.dualRestrict_comp {I : X.IdealSheafData} {U V W : X.affineOpens}
    (hW : CartierChart I W) (hVW : V ≤ W) (hUV : U ≤ V)
    (f : divisorChartModule I W) :
    (hW.mono hVW).dualRestrict hUV (hW.dualRestrict hVW f) =
      hW.dualRestrict (hUV.trans hVW) f := by
  have he : (X.presheaf.map (homOfLE (show U.1 ≤ V.1 from hUV)).op).hom.comp
      (X.presheaf.map (homOfLE (show V.1 ≤ W.1 from hVW)).op).hom =
      (X.presheaf.map (homOfLE (show U.1 ≤ W.1 from hUV.trans hVW)).op).hom := by
    rw [← CommRingCat.hom_comp, ← Functor.map_comp]
    rfl
  apply hW.dual_ext_restrict (hUV.trans hVW)
  intro x
  have hx : CartierModule.idealRestrict _ _ _ (I.map_ideal (hUV.trans hVW)).le x =
      CartierModule.idealRestrict _ _ _ (I.map_ideal hUV).le
        (CartierModule.idealRestrict _ _ _ (I.map_ideal hVW).le x) :=
    Subtype.ext (congrArg (fun σ ↦ σ (x : Γ(X, W))) he.symm)
  rw [CartierChart.dualRestrict_apply, hx, CartierChart.dualRestrict_apply,
    CartierChart.dualRestrict_apply]
  exact congrArg (fun σ ↦ σ (f x)) he

/-- The sum comparison evaluates on an actual product of ideal sections. -/
lemma CartierChart.sumEquiv_apply {I J : X.IdealSheafData} {U : X.affineOpens}
    (hI : CartierChart I U) (hJ : CartierChart J U)
    (f : divisorChartModule I U) (g : divisorChartModule J U)
    (x : I.ideal U) (y : J.ideal U) :
    hI.sumEquiv hJ (f ⊗ₜ[Γ(X, U)] g)
      ⟨(x : Γ(X, U)) * y, Ideal.mul_mem_mul x.property y.property⟩ = f x * g y := by
  have he := CartierModule.dualTensorEquiv_apply _ _ _ _
    hI.choose_spec.1 hJ.choose_spec.1 hI.choose_spec.2 hJ.choose_spec.2 f g x y
  have hx := CartierModule.idealTensorEquiv_tmul _ _ _ _
    hI.choose_spec.1 hJ.choose_spec.1 hI.choose_spec.2 hJ.choose_spec.2 x y
  exact (congrArg (CartierModule.dualTensorEquiv _ _ _ _ hI.choose_spec.1
    hJ.choose_spec.1 hI.choose_spec.2 hJ.choose_spec.2 (f ⊗ₜ g))
    (Subtype.ext hx)).symm.trans he

/-- Restriction commutes with the sum comparison on pure tensors. -/
lemma CartierChart.dualRestrict_sumEquiv {I J : X.IdealSheafData}
    {U V : X.affineOpens} (hI : CartierChart I V) (hJ : CartierChart J V)
    (hUV : U ≤ V) (f : divisorChartModule I V) (g : divisorChartModule J V) :
    (hI.mul hJ).dualRestrict hUV (hI.sumEquiv hJ (f ⊗ₜ[Γ(X, V)] g)) =
      (hI.mono hUV).sumEquiv (hJ.mono hUV)
        (hI.dualRestrict hUV f ⊗ₜ[Γ(X, U)] hJ.dualRestrict hUV g) := by
  apply (hI.mul hJ).dual_ext_restrict hUV
  intro z
  obtain ⟨r, hr⟩ := (CartierModule.idealEquiv _ _
    (hI.choose_spec.1.mul hJ.choose_spec.1)
    (by change I.ideal V * J.ideal V = _
        exact (congrArg₂ (· * ·) hI.choose_spec.2 hJ.choose_spec.2).trans
          (Ideal.span_singleton_mul_span_singleton _ _))
    ).surjective z
  let x := hI.idealEquiv r
  let y := hJ.idealEquiv 1
  have hz : z = ⟨(x : Γ(X, V)) * y, Ideal.mul_mem_mul x.property y.property⟩ := by
    rw [← hr]
    apply Subtype.ext
    simp [x, y, CartierChart.idealEquiv, mul_assoc]
  rw [hz, CartierChart.dualRestrict_apply, CartierChart.sumEquiv_apply, map_mul]
  have hp : CartierModule.idealRestrict _ _ _ ((I * J).map_ideal hUV).le
      ⟨(x : Γ(X, V)) * y, Ideal.mul_mem_mul x.property y.property⟩ =
      ⟨_, Ideal.mul_mem_mul
        (CartierModule.idealRestrict _ _ _ (I.map_ideal hUV).le x).property
        (CartierModule.idealRestrict _ _ _ (J.map_ideal hUV).le y).property⟩ :=
    Subtype.ext (map_mul _ _ _)
  rw [hp, CartierChart.sumEquiv_apply, CartierChart.dualRestrict_apply,
    CartierChart.dualRestrict_apply]

/-- The affine section isomorphism carries the image ideal to the pulled back ideal. -/
lemma ideal_map_appIso (I : Y.IdealSheafData) (f : X ⟶ Y) [IsOpenImmersion f]
    (U : X.affineOpens) :
    (I.ideal ⟨f ''ᵁ U, U.2.image_of_isOpenImmersion f⟩).map
      (f.appIso U).commRingCatIsoToRingEquiv = (I.comap f).ideal U := by
  rw [I.ideal_comap_of_isOpenImmersion]
  exact Ideal.map_comap_of_equiv (f.appIso U).commRingCatIsoToRingEquiv

/-- Open immersions transport dual ideal modules by their affine ring isomorphisms. -/
def divisorChartTransport (I : Y.IdealSheafData) (f : X ⟶ Y) [IsOpenImmersion f]
    (U : X.affineOpens) :
    divisorChartModule I ⟨f ''ᵁ U, U.2.image_of_isOpenImmersion f⟩ ≃ₛₗ[
      ((f.appIso U).commRingCatIsoToRingEquiv : Γ(Y, f ''ᵁ U) →+* Γ(X, U))]
        divisorChartModule (I.comap f) U :=
  CartierModule.dualTransport _ _ _ (ideal_map_appIso I f U)

lemma divisorChartTransport_apply (I : Y.IdealSheafData) (f : X ⟶ Y)
    [IsOpenImmersion f] (U : X.affineOpens)
    (s : divisorChartModule I ⟨f ''ᵁ U, U.2.image_of_isOpenImmersion f⟩)
    (x : I.ideal ⟨f ''ᵁ U, U.2.image_of_isOpenImmersion f⟩) :
    divisorChartTransport I f U s
      (CartierModule.idealRestrict _ _ _ (ideal_map_appIso I f U).le x) =
        (f.appIso U).hom.hom (s x) :=
  CartierModule.dualTransport_apply _ _ _ _ s x

/-- Open-immersion transport commutes with restriction between affine charts. -/
lemma divisorChartTransport_naturality (I : Y.IdealSheafData) (f : X ⟶ Y)
    [IsOpenImmersion f] {U V : X.affineOpens} (hUV : U ≤ V)
    (hV : CartierChart I ⟨f ''ᵁ V, V.2.image_of_isOpenImmersion f⟩)
    (s : divisorChartModule I ⟨f ''ᵁ V, V.2.image_of_isOpenImmersion f⟩) :
    divisorChartTransport I f U
      (hV.dualRestrict (show f ''ᵁ U ≤ f ''ᵁ V from Set.image_mono hUV) s) =
      ((cartierChart_comap_iff I f V).mpr hV).dualRestrict hUV
        (divisorChartTransport I f V s) := by
  let himg : f ''ᵁ U ≤ f ''ᵁ V := Set.image_mono hUV
  have hn (a : Γ(Y, f ''ᵁ V)) :
      (f.appIso U).hom.hom ((Y.presheaf.map (homOfLE himg).op).hom a) =
      (X.presheaf.map (homOfLE (show U.1 ≤ V.1 from hUV)).op).hom
        ((f.appIso V).hom.hom a) :=
    congrArg (fun k ↦ k.hom a) (f.appIso_hom_naturality (homOfLE hUV).op)
  apply ((cartierChart_comap_iff I f V).mpr hV).dual_ext_restrict hUV
  intro x
  obtain ⟨y, rfl⟩ := (CartierModule.idealTransport _ _ _
    (ideal_map_appIso I f V)).surjective x
  rw [CartierChart.dualRestrict_apply]
  have hx : CartierModule.idealRestrict _ _ _ ((I.comap f).map_ideal hUV).le
      (CartierModule.idealTransport _ _ _ (ideal_map_appIso I f V) y) =
      CartierModule.idealRestrict _ _ _ (ideal_map_appIso I f U).le
        (CartierModule.idealRestrict _ _ _ (I.map_ideal himg).le y) :=
    Subtype.ext (hn (y : Γ(Y, f ''ᵁ V))).symm
  rw [hx, divisorChartTransport_apply, CartierChart.dualRestrict_apply]
  change _ = (X.presheaf.map (homOfLE (show U.1 ≤ V.1 from hUV)).op).hom
    (divisorChartTransport I f V s
      (CartierModule.idealRestrict _ _ _ (ideal_map_appIso I f V).le y))
  rw [divisorChartTransport_apply]
  exact hn (s y)

end FLT.Mazur.FCurve
