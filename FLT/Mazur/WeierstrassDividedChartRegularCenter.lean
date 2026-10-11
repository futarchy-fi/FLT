/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassRetainedRegularCenter
public import FLT.Mazur.WeierstrassDividedDepthLocalAction
public import FLT.Mazur.WeierstrassDividedInitialExterior

/-!
# Deeper regular centers on actual finite-depth equation charts

The flatness used here is that of the input chart projection. No flatness
of an arbitrarily chosen coefficient algebra is assumed.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R S : Type u} [CommRing R] [IsDomain R] [CommRing S]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0)

omit [IsDomain R] in
/-- Equality of original affine-chart points detects their ring presentations. -/
theorem originalPresentation_eq {A : Type u} [CommRing A]
    (c : Coordinate W 2 →+* A) (g : Spec (.of S) ⟶ Spec (.of A))
    (β : Coordinate W 2 →+* S)
    (he : Spec.map (CommRingCat.ofHom β) ≫ integralCurveChart W 2 =
      g ≫ Spec.map (CommRingCat.ofHom c) ≫ integralCurveChart W 2) :
    β = (affineChartRingHom g).comp c := by
  rw [← affineChartRingHom_spec g, ← Spec.map_comp_assoc] at he
  exact congrArg CommRingCat.Hom.hom
    (Spec.map_injective ((cancel_mono (integralCurveChart W 2)).mp he))

include hπ in
/-- A flat map into the original exterior has a regular deeper center at any later depth. -/
theorem initialExterior_regularCenter {start k : ℕ} (d : Data W π start) (hk : start ≤ k)
    (g : Spec (.of S) ⟶ (initialExterior d).carrier) [Flat g]
    (β : Coordinate W 2 →+* S)
    (he : Spec.map (CommRingCat.ofHom β) ≫ integralCurveChart W 2 =
      g ≫ (initialExterior d).exteriorChart ≫ initialToCurve d) :
    ∃ x : S, IsRegular x ∧ (modificationChartCenter W (π ^ k * π) 2).map β =
      Ideal.span {x} ∧ β (algebraMap R _ (π ^ k)) ∈ Ideal.span {x} := by
  let ψ := affineChartRingHom g
  have hψ : RingHom.Flat ψ := by
    apply (Flat.SpecMap_iff (f := CommRingCat.ofHom ψ)).mp
    rw [affineChartRingHom_spec]
    infer_instance
  have hb : β = ψ.comp (WeierstrassModificationX.fromOriginal W (π ^ start)
      d.b3 d.b4 d.b6 d.factor3 d.factor4 d.factor6).toRingHom := by
    apply originalPresentation_eq _ g β
    simpa only [initialToCurve_exterior, WeierstrassModificationX.toCurve] using he
  have hscale : π ^ start * π ^ (k - start) = π ^ k := by
    rw [← pow_add, Nat.add_sub_of_le hk]
  obtain ⟨x, hx, hc, hs⟩ := WeierstrassSuccessiveX.exteriorPresentation_regularCenter
    W (π ^ start) π d.b3 d.b4 d.b6 d.factor3 d.factor4 d.factor6
    (pow_ne_zero _ hπ) (π ^ (k - start)) ψ hψ
  rw [hscale] at hc hs
  refine ⟨x, hx, ?_, ?_⟩
  · simpa only [hb] using hc
  · rw [hb]
    change ψ ((WeierstrassModificationX.fromOriginal W (π ^ start)
      d.b3 d.b4 d.b6 d.factor3 d.factor4 d.factor6) (algebraMap R _ (π ^ k))) ∈
        Ideal.span {x}
    rw [AlgHom.commutes]
    exact hs

/-- The actual successive x contraction retains its normalized original ring presentation. -/
@[reassoc] theorem xContraction_originalPresentation {m : ℕ}
    (d : Data W π m) (e : Data W π (m + 1)) :
    xContraction hπ d e ≫ toCurve d =
      Spec.map (CommRingCat.ofHom ((WeierstrassSuccessiveX.fromDivided W (π ^ m) π
        e.b3 e.b4 e.b6).comp (previousOriginalMap hπ d e)).toRingHom) ≫
          integralCurveChart W 2 := by
  have hn : xContraction hπ d e =
      WeierstrassSuccessiveX.toDivided W (π ^ m) π e.b3 e.b4 e.b6 ≫
        (previousChartIso hπ d e).hom := by
    unfold xContraction previousChartIso WeierstrassSuccessiveX.previousDepthEquiv
      WeierstrassDilatation.parameterSpecIso
    rfl
  rw [hn, Category.assoc, previousChartIso_toCurve]
  change Spec.map _ ≫ (Spec.map _ ≫ _) = _
  rw [← Spec.map_comp_assoc]
  rfl

/-- A flat successive x input has a regular center and divides every later output scale. -/
theorem stepX_regularCenter {m k : ℕ} (d : Data W π m) (e : Data W π (m + 1))
    (hk : m + 1 ≤ k) (g : Spec (.of S) ⟶ stepX e) [Flat g]
    (β : Coordinate W 2 →+* S)
    (he : Spec.map (CommRingCat.ofHom β) ≫ integralCurveChart W 2 =
      g ≫ xContraction hπ d e ≫ toCurve d) :
    ∃ x : S, IsRegular x ∧ (modificationChartCenter W (π ^ k * π) 2).map β =
      Ideal.span {x} ∧ β (algebraMap R _ (π ^ k)) ∈ Ideal.span {x} := by
  let ψ := affineChartRingHom g
  have hψ : RingHom.Flat ψ := by
    apply (Flat.SpecMap_iff (f := CommRingCat.ofHom ψ)).mp
    rw [affineChartRingHom_spec]
    infer_instance
  have hb : β = ψ.comp ((WeierstrassSuccessiveX.fromDivided W (π ^ m) π
      e.b3 e.b4 e.b6).comp (previousOriginalMap hπ d e)).toRingHom := by
    apply originalPresentation_eq _ g β
    simpa only [xContraction_originalPresentation] using he
  have hscale : π ^ m * (π * π ^ (k - (m + 1))) = π ^ k := by
    rw [← mul_assoc, ← pow_succ, ← pow_add, Nat.add_sub_of_le hk]
  obtain ⟨x, hx, hc, hs⟩ := WeierstrassSuccessiveX.successivePresentation_regularCenter
    W (π ^ m) π e.b3 e.b4 e.b6
    (by rw [← factor3_step hπ d e]; exact d.factor3)
    (by rw [← factor4_step hπ d e]; exact d.factor4)
    (by rw [← factor6_step hπ d e]; exact d.factor6)
    hπ (pow_ne_zero _ hπ) (π ^ (k - (m + 1))) ψ hψ
  rw [hscale] at hc hs
  refine ⟨x, hx, ?_, ?_⟩
  · simpa only [hb, previousOriginalMap] using hc
  · rw [hb]
    change ψ (((WeierstrassSuccessiveX.fromDivided W (π ^ m) π e.b3 e.b4 e.b6).comp
      (previousOriginalMap hπ d e)) (algebraMap R _ (π ^ k))) ∈ Ideal.span {x}
    rw [AlgHom.commutes]
    exact hs

end FLT.Mazur.WeierstrassDividedDepth
