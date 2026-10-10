/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.TensorOpenChartIntersection

/-!
# Full tensor intersections with a possibly nonaffine exterior

Base change retains the entire exterior. An original principal intersection
with an affine chart gives its exact tensor principal preimage and a
cartesian square with a canonical map back to the exterior.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
open scoped TensorProduct
namespace FLT.Mazur.TensorOpenExterior
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] (S : Type u) [CommRing S] [Algebra R S]
  {X E : Scheme.{u}} (f : X ⟶ Spec (.of R)) (i : E ⟶ X)
local notation "q" => Spec.map (CommRingCat.ofHom (algebraMap R S))

/-- The entire exterior base change embeds by the original exterior inclusion. -/
def inclusion : pullback q (i ≫ f) ⟶ pullback q f :=
  pullback.map _ _ _ _ (𝟙 _) i (𝟙 _) (by simp) (by simp)

/-- The exterior inclusion retains every original function. -/
@[reassoc] theorem inclusion_snd :
    inclusion S f i ≫ pullback.snd q f = pullback.snd q (i ≫ f) ≫ i :=
  pullback.lift_snd _ _ _

/-- The exterior inclusion retains the extended coefficients. -/
@[reassoc] theorem inclusion_fst :
    inclusion S f i ≫ pullback.fst q f = pullback.fst q (i ≫ f) := by
  simp only [inclusion, pullback.lift_fst, Category.comp_id]

/-- The full exterior inclusion is the cartesian base change of the original map. -/
theorem inclusion_isPullback :
    IsPullback (inclusion S f i) (pullback.snd q (i ≫ f)) (pullback.snd q f) i := by
  apply IsPullback.of_right (h₁₂ := pullback.fst _ _) (h₂₂ := f) _
    (inclusion_snd S f i) (.of_hasPullback _ _)
  rw [inclusion_fst]
  exact .of_hasPullback _ _

instance inclusion_isOpenImmersion [IsOpenImmersion i] :
    IsOpenImmersion (inclusion S f i) := by
  unfold inclusion
  infer_instance

/-- The full inverse image of the original exterior, with no component omitted. -/
theorem inclusion_range :
    Set.range (inclusion S f i) = (pullback.snd q f) ⁻¹' Set.range i := by
  ext z
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨pullback.snd q (i ≫ f) a,
      (congrArg (fun g => g a) (inclusion_snd S f i)).symm⟩
  · rintro ⟨a, ha⟩
    obtain ⟨b, hb, _⟩ := Scheme.exists_preimage_of_isPullback
      (inclusion_isPullback S f i) z a ha.symm
    exact ⟨b, hb⟩

variable {A : Type u} [CommRing A] [Algebra R A] (j : Spec (.of A) ⟶ X)
  (hj : j ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R A))) (x : A)
  (hp : j ⁻¹' Set.range i = Set.range
    (Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away x)))))

include hp in
/-- The original exact principal intersection survives on the whole tensor algebra. -/
theorem principal_preimage :
    TensorOpenChart.chart (S := S) f j hj ⁻¹' Set.range (inclusion S f i) =
      Set.range (PrincipalOpenTensor.inclusion S x) := by
  rw [inclusion_range]
  have he : TensorOpenChart.chart (S := S) f j hj ⁻¹'
      ((pullback.snd q f) ⁻¹' Set.range i) =
        TensorOpenChart.projection ⁻¹' (j ⁻¹' Set.range i) := by
    ext z
    change pullback.snd q f (TensorOpenChart.chart f j hj z) ∈ Set.range i ↔ _
    rw [← Scheme.Hom.comp_apply, TensorOpenChart.chart_snd]
    rfl
  rw [he, hp]
  change TensorOpenChart.projection ⁻¹' Set.range
    (PrimeSpectrum.comap (algebraMap A (Localization.Away x))) =
      Set.range (PrimeSpectrum.comap
        (algebraMap (S ⊗[R] A) (Localization.Away ((1 : S) ⊗ₜ[R] x))))
  rw [PrimeSpectrum.localization_away_comap_range _ x,
    PrimeSpectrum.localization_away_comap_range _ ((1 : S) ⊗ₜ[R] x)]
  rfl

variable [IsOpenImmersion i]

/-- The full tensor principal overlap has its canonical map to the extended exterior. -/
def principalToExterior :
    Spec (.of (Localization.Away ((1 : S) ⊗ₜ[R] x))) ⟶ pullback q (i ≫ f) :=
  IsOpenImmersion.lift (inclusion S f i)
    (PrincipalOpenTensor.inclusion S x ≫ TensorOpenChart.chart f j hj) (by
      rintro z ⟨a, rfl⟩
      exact Set.ext_iff.mp (principal_preimage S f i j hj x hp)
        (PrincipalOpenTensor.inclusion S x a) |>.mpr ⟨a, rfl⟩)

/-- The canonical overlap map retains the actual ambient tensor inclusion. -/
@[reassoc] theorem principalToExterior_comp :
    principalToExterior S f i j hj x hp ≫ inclusion S f i =
      PrincipalOpenTensor.inclusion S x ≫ TensorOpenChart.chart f j hj :=
  IsOpenImmersion.lift_fac _ _ _

/-- The full original tensor principal open is the actual exterior-chart fiber product. -/
theorem principal_isPullback :
    IsPullback (principalToExterior S f i j hj x hp) (PrincipalOpenTensor.inclusion S x)
      (inclusion S f i) (TensorOpenChart.chart f j hj) := by
  apply IsOpenImmersion.isPullback
  · exact (principalToExterior_comp S f i j hj x hp).symm
  · exact TopologicalSpace.Opens.ext (principal_preimage S f i j hj x hp)

end FLT.Mazur.TensorOpenExterior
