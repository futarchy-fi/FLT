/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassConicZeroDescent
public import FLT.Mazur.WeierstrassConicZeroAffineParameter
public import FLT.Mazur.PrincipalOpenVanishingIntersection
public import FLT.Mazur.PrincipalOpenTransportGeometry

/-!
# The two original Laurent punctures cover the full zero-conic boundary

This works over any coefficient field, including the actual tangent extension.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
open scoped Polynomial LaurentPolynomial
namespace FLT.Mazur.WeierstrassSuccessiveX
open WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option quotPrecheck false
universe u
variable {K : Type u} [Field K] (W : WeierstrassCurve K) (c : K)
  (ha : IsUnit W.a₁) (hc : c = 0)
local notation "C₀" => ConicCoordinate W.a₁ c
local notation "inc" => PrincipalOpenTransport.inclusion (conicT W.a₁ c)
local notation "Z" => conicZeroAffineIso c hc
local notation "p₁" => (conicFirstParameterIso W.a₁ c ha).inv ≫
  conicFirstOpenImmersion W.a₁ c
local notation "p₂" => (conicSecondParameterIso W.a₁ c ha).inv ≫
  conicSecondOpenImmersion W.a₁ c
local notation "f₁" => (Z).hom ≫ p₁
local notation "f₂" => (Z).hom ≫ p₂
local notation "b₁" => Spec.map (CommRingCat.ofHom
  (conicBoundaryFirst W c ha hc).toRingHom)
local notation "b₂" => Spec.map (CommRingCat.ofHom
  (conicBoundarySecond W c ha hc).toRingHom)
local notation "p" => ProjectiveLine.overlapLeft K

/-- The first original puncture is the restriction of its entire affine parameter. -/
@[reassoc] theorem conicZeroBoundaryFirst_parameter : b₁ ≫ inc = p ≫ f₁ := by
  rw [← Category.assoc, conicZeroAffineIso_puncture]
  exact conicBoundaryFirst_inclusion W c ha hc

/-- The opposite original puncture retains its entire signed affine parameter. -/
@[reassoc] theorem conicZeroBoundarySecond_parameter : b₂ ≫ inc = p ≫ f₂ := by
  rw [← Category.assoc, conicZeroAffineIso_puncture]
  exact conicBoundarySecond_inclusion W c ha hc

instance conicZeroBoundaryFirst_isOpenImmersion : IsOpenImmersion b₁ := by
  have : IsOpenImmersion (b₁ ≫ inc) := by
    rw [conicZeroBoundaryFirst_parameter]
    infer_instance
  exact IsOpenImmersion.of_comp _ inc

instance conicZeroBoundarySecond_isOpenImmersion : IsOpenImmersion b₂ := by
  have : IsOpenImmersion (b₂ ≫ inc) := by
    rw [conicZeroBoundarySecond_parameter]
    infer_instance
  exact IsOpenImmersion.of_comp _ inc

local notation "q₁" => (conicZeroAffineEquiv c hc).toAlgHom.comp
  ((conicFirstParameterEquiv W.a₁ c ha).symm.toAlgHom.comp (Algebra.algHom K C₀ _))
local notation "q₂" => (conicZeroAffineEquiv c hc).toAlgHom.comp
  ((conicSecondParameterEquiv W.a₁ c ha).symm.toAlgHom.comp (Algebra.algHom K C₀ _))

/-- The first full parameter sends incidence to its original nonzero tangent scale. -/
theorem conicZeroFirstParameter_incidence :
    q₁ (conicT W.a₁ c) = Polynomial.C W.a₁ * Polynomial.X := by
  change conicZeroAffineEquiv c hc
    (conicFirstToParameter W.a₁ c ha (algebraMap C₀ _ (conicT W.a₁ c))) = _
  rw [conicFirstToParameter_base, conicToParameter_t, conicInverseT,
    conicParameterInv_of_zero c hc, mul_one, map_mul, AlgEquiv.commutes]
  congr 1
  exact conicZeroAffineEquiv_base c hc Polynomial.X

/-- The opposite full parameter retains the negative tangent scale on incidence. -/
theorem conicZeroSecondParameter_incidence :
    q₂ (conicT W.a₁ c) = Polynomial.C (-W.a₁) * Polynomial.X := by
  change conicZeroAffineEquiv c hc
    ((conicSecondParameterEquiv W.a₁ c ha).symm
      (algebraMap C₀ _ (conicT W.a₁ c))) = _
  rw [conicSecondParameterEquiv_symm_t, conicInverseT,
    conicParameterInv_of_zero c hc, mul_one, map_mul, AlgEquiv.commutes]
  congr 1
  exact conicZeroAffineEquiv_base c hc Polynomial.X

/-- A nonzero incidence scale pulls the full boundary back to the standard Laurent open. -/
theorem conicZeroParameter_incidence_preimage (q : C₀ →ₐ[K] K[X]) (a : K) (ha : IsUnit a)
    (ht : q (conicT W.a₁ c) = Polynomial.C a * Polynomial.X) :
    (Spec.map (CommRingCat.ofHom q.toRingHom)) ⁻¹' Set.range inc = Set.range p := by
  unfold PrincipalOpenTransport.inclusion
  rw [PrincipalOpenVanishingIntersection.preimage q.toRingHom (conicT W.a₁ c)]
  rw [show Set.range p = (PrimeSpectrum.basicOpen (Polynomial.X : K[X]) :
      Set (PrimeSpectrum K[X])) from PrimeSpectrum.localization_away_comap_range _ _]
  ext x
  change q (conicT W.a₁ c) ∉ x.asIdeal ↔ Polynomial.X ∉ x.asIdeal
  rw [ht, x.isPrime.mul_mem_iff_mem_or_mem]
  have h : Polynomial.C a ∉ x.asIdeal := fun h =>
    x.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ h (ha.map Polynomial.C))
  simp only [h, false_or]

/-- The first parameter meets the full incidence boundary precisely in its Laurent puncture. -/
theorem conicZeroFirstParameter_preimage : f₁ ⁻¹' Set.range inc = Set.range p := by
  have H : f₁ = Spec.map (CommRingCat.ofHom (q₁).toRingHom) := by
    change Spec.map _ ≫ Spec.map _ ≫ Spec.map _ = _
    rw [← Spec.map_comp, ← Spec.map_comp]
    rfl
  rw [H]
  exact conicZeroParameter_incidence_preimage W c q₁ W.a₁ ha
    (conicZeroFirstParameter_incidence W c ha hc)

/-- The opposite parameter has the same full puncture preimage with its original sign. -/
theorem conicZeroSecondParameter_preimage : f₂ ⁻¹' Set.range inc = Set.range p := by
  have H : f₂ = Spec.map (CommRingCat.ofHom (q₂).toRingHom) := by
    change Spec.map _ ≫ Spec.map _ ≫ Spec.map _ = _
    rw [← Spec.map_comp, ← Spec.map_comp]
    rfl
  rw [H]
  exact conicZeroParameter_incidence_preimage W c q₂ (-W.a₁) ha.neg
    (conicZeroSecondParameter_incidence W c ha hc)

/-- The two actual punctures cover every point of the original full conic incidence open. -/
theorem conicZeroBoundary_cover (x : Spec (.of (MiddleConicOpen W c))) :
    x ∈ Set.range b₁ ∨ x ∈ Set.range b₂ := by
  have hf (y : Spec (.of C₀)) : y ∈ Set.range f₁ ∨ y ∈ Set.range f₂ := by
    rcases conicZeroParameterCharts_cover W.a₁ c ha hc y with ⟨z, hz⟩ | ⟨z, hz⟩
    · exact Or.inl ⟨(Z).inv z, by simpa using hz⟩
    · exact Or.inr ⟨(Z).inv z, by simpa using hz⟩
  rcases hf (inc x) with ⟨z, hz⟩ | ⟨z, hz⟩
  · have hz' : z ∈ Set.range p := by
      rw [← conicZeroFirstParameter_preimage W c ha hc]
      exact ⟨x, hz.symm⟩
    obtain ⟨t, rfl⟩ := hz'
    left
    refine ⟨t, (inc).isOpenEmbedding.injective ?_⟩
    change (b₁ ≫ inc) t = inc x
    rw [conicZeroBoundaryFirst_parameter]
    exact hz
  · have hz' : z ∈ Set.range p := by
      rw [← conicZeroSecondParameter_preimage W c ha hc]
      exact ⟨x, hz.symm⟩
    obtain ⟨t, rfl⟩ := hz'
    right
    refine ⟨t, (inc).isOpenEmbedding.injective ?_⟩
    change (b₂ ≫ inc) t = inc x
    rw [conicZeroBoundarySecond_parameter]
    exact hz

/-- Both whole punctures detect equality into arbitrary, possibly nonseparated, schemes. -/
theorem conicZeroBoundary_hom_ext {Y : Scheme.{u}}
    (f g : Spec (.of (MiddleConicOpen W c)) ⟶ Y)
    (h₁ : b₁ ≫ f = b₁ ≫ g) (h₂ : b₂ ≫ f = b₂ ≫ g) : f = g :=
  BinaryOpenDescent.hom_ext b₁ b₂ (conicZeroBoundary_cover W c ha hc) f g h₁ h₂

end FLT.Mazur.WeierstrassSuccessiveX
