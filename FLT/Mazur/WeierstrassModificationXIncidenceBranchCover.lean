/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationXFullNodeIncidenceBranch
public import FLT.Mazur.NodePinchingExistence

/-!
# The two original localized incidence branches cover the entire slope line

The opposite branch keeps its translation by minus the tangent. After this
translation its omitted point is zero; the first branch contains zero.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Polynomial
namespace FLT.Mazur.WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
universe u
variable {K : Type u} [Field K] (a c : K) (ha : IsUnit a)
local notation "s₁" => PolygonNodeEqualizer.second (fullNodeNormalizedDenominator a c)
local notation "s₂" => PolygonNodeEqualizer.second (fullNodeNormalizedDenominator (-a) c)
local notation "b₁" => NodeLocalDescent.branchOpen K s₁
local notation "b₂" => NodeLocalDescent.branchOpen K s₂
local notation "t" => Spec.map (CommRingCat.ofHom
  (AlgHom.toRingHom (aeval (X - C a) : K[X] →ₐ[K] K[X])))
local notation "v" => Spec.map (CommRingCat.ofHom
  (AlgHom.toRingHom (aeval (X + C a) : K[X] →ₐ[K] K[X])))

/-- The two opposite affine slope translations cancel on the whole scheme. -/
@[reassoc] theorem fullNodeIncidenceTranslation_cancel : v ≫ t = 𝟙 _ := by
  rw [← Spec.map_comp]
  have h : (aeval (X + C a : K[X])).comp (aeval (X - C a)) = AlgHom.id K K[X] := by
    ext
    simp
  change Spec.map (CommRingCat.ofHom
    ((aeval (X + C a : K[X])).comp (aeval (X - C a))).toRingHom) = _
  rw [h]
  exact Spec.map_id _

/-- Translation of the opposite incidence parameter is an isomorphism. -/
instance fullNodeIncidenceTranslation_isIso : IsIso t := by
  have hv : t ≫ v = 𝟙 _ := by
    simpa only [map_neg, sub_eq_add_neg, neg_neg] using
      fullNodeIncidenceTranslation_cancel (-a)
  exact ⟨⟨v, hv, fullNodeIncidenceTranslation_cancel a⟩⟩

include ha in
/-- The full original two incidence branches jointly cover the affine slope line. -/
theorem fullNodeIncidenceBranches_cover (z : ProjectiveLine.chart K) :
    z ∈ Set.range b₁ ∨ z ∈ Set.range (b₂ ≫ t) := by
  by_cases h : s₁ ∉ z.asIdeal
  · left
    exact (PrimeSpectrum.localization_away_comap_range (Localization.Away s₁) s₁).symm ▸ h
  · have hs : s₁ ∈ z.asIdeal := not_not.mp h
    have hX : (X : K[X]) ∉ z.asIdeal := by
      intro hx
      have hm : X + C a ∈ z.asIdeal := by
        have hu : IsUnit (C a⁻¹ : K[X]) := ha.inv.map C
        rw [fullNodeNormalizedDenominator_second] at hs
        exact (z.isPrime.mem_or_mem hs).resolve_left
          (fun hc => z.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hc hu))
      have hc : C a ∈ z.asIdeal := by simpa using z.asIdeal.sub_mem hm hx
      exact z.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hc (ha.map C))
    have hy : s₂ ∉ (v z).asIdeal := by
      change aeval (X + C a : K[X]) s₂ ∉ z.asIdeal
      rw [fullNodeNormalizedDenominator_second]
      simp only [map_mul, map_add, aeval_C, aeval_X, map_neg, Polynomial.algebraMap_eq,
        add_neg_cancel_right]
      intro hm
      rcases z.isPrime.mem_or_mem hm with hc | hx
      · exact z.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hc (ha.neg.inv.map C))
      · exact hX hx
    have hy' : v z ∈ Set.range b₂ :=
      (PrimeSpectrum.localization_away_comap_range (Localization.Away s₂) s₂).symm ▸ hy
    obtain ⟨y, hy⟩ := hy'
    right
    refine ⟨y, ?_⟩
    change t (b₂ y) = z
    rw [hy]
    exact congrArg (fun f => f z) (fullNodeIncidenceTranslation_cancel a)

include ha in
/-- Equality on the two exact localized branches determines every affine incidence map. -/
theorem fullNodeIncidenceBranches_hom_ext {Y : Scheme.{u}}
    (f g : ProjectiveLine.chart K ⟶ Y)
    (h₁ : b₁ ≫ f = b₁ ≫ g) (h₂ : b₂ ≫ t ≫ f = b₂ ≫ t ≫ g) : f = g := by
  apply BinaryOpenDescent.hom_ext b₁ (b₂ ≫ t) (fullNodeIncidenceBranches_cover a c ha)
  · exact h₁
  · simpa only [Category.assoc] using h₂

end FLT.Mazur.WeierstrassModificationX
