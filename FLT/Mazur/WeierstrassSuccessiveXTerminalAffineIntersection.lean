/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSuccessiveXTerminalAffineCover
public import FLT.Mazur.WeierstrassModificationXConicBoundaryIntersection

/-!
# The complete intersection of the two terminal affine charts

No extra points occur in the intersection: it is exactly the entire
original Laurent chart, with the ordered scaled reciprocal coordinates.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
open scoped Polynomial LaurentPolynomial
namespace FLT.Mazur.WeierstrassSuccessiveX
open WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} {n : ℕ} (D : SplitNodeDepth W π n)
  (k : ℕ) (hk : 2 * (k + 1) ≤ n) (b3 b4 b6 : R)
  (h3 : W.a₃ = π ^ (k + 1) * b3) (h4 : W.a₄ = π ^ (k + 1) * b4)
  (h6 : W.a₆ = (π ^ (k + 1)) ^ 2 * b6) (hp : 2 * (k + 1) = n)
local notation "K" => ResidueField R
local notation "a" => WeierstrassCurve.a₁ (W.map (residue R))
local notation "c" => residue R b6
local notation "ha" => D.a₁_unit.map (residue R)
local notation "hc" => laurentConicComponent_constant_isUnit D k b6 h6 hp
local notation "P" => laurentConicComponent D k hk b3 b4 b6 h3 h4 h6 hp
local notation "l" => laurentConicComponentConic D k hk b3 b4 b6 h3 h4 h6 hp
local notation "r" => laurentConicComponentTorus D k hk b3 b4 b6 h3 h4 h6 hp
local notation "j" => PrincipalOpenTransport.inclusion (conicParameterPolynomial c)
local notation "f" => laurentConicComponentFirstAffine D k hk b3 b4 b6 h3 h4 h6 hp
local notation "g" => laurentConicComponentSecondAffine D k hk b3 b4 b6 h3 h4 h6 hp

local notation "i" => Spec.map (CommRingCat.ofHom
  (algebraMap (ConicCoordinate a c) (ConicIncidenceOpen a c)))
local notation "ψ" => residueLaurentConicMap D k hk b3 b4 b6 h3 h4 h6 hp
local notation "s" => Spec.map (CommRingCat.ofHom (AlgHom.toRingHom ψ))
local notation "q₁" => laurentConicComponentFirstParameter D k hk b3 b4 b6 h3 h4 h6 hp
local notation "q₂" => laurentConicComponentSecondParameter D k hk b3 b4 b6 h3 h4 h6 hp

/-- An intersection of the original parameter neighborhoods is on the full torus. -/
theorem laurentConicComponentParameters_intersection {x y : Spec (.of (ConicParameterOpen c))}
    (h : q₁ x = q₂ y) : q₂ y ∈ Set.range r := by
  let x' := (conicFirstParameterIso a c ha).inv x
  let y' := (conicSecondParameterIso a c ha).inv y
  have he : conicFirstOpenImmersion a c x' = conicSecondOpenImmersion a c y' :=
    (l).isOpenEmbedding.injective h
  have hi : conicSecondOpenImmersion a c y' ∈ Set.range i :=
    conicTangent_intersection_subset_incidence a c ⟨⟨x', he⟩, ⟨y', rfl⟩⟩
  obtain ⟨z, hz⟩ := hi
  refine ⟨s z, ?_⟩
  rw [← Scheme.Hom.comp_apply, ← laurentConicComponent_condition]
  change l (i z) = l (conicSecondOpenImmersion a c y')
  exact congrArg l hz

/-- The completed affine charts intersect precisely in the entire original Laurent chart. -/
theorem laurentConicComponentAffine_intersection :
    Set.range f ∩ Set.range g = Set.range r := by
  apply Set.Subset.antisymm
  · rintro z ⟨⟨x, rfl⟩, y, hy⟩
    rcases ProjectiveLine.conicParameter_scaledTorus_cover K c ((hc).unit)⁻¹ x with
      ⟨x', rfl⟩ | ⟨x', rfl⟩
    · rcases terminalSecondAffine_cover b6 y with ⟨y', rfl⟩ | ⟨y', rfl⟩
      · change g (j y') = f (j x') at hy
        change f (j x') ∈ Set.range r
        simp only [← Scheme.Hom.comp_apply, laurentConicComponentFirstAffine_parameter,
          laurentConicComponentSecondAffine_parameter] at hy ⊢
        rw [← hy]
        exact laurentConicComponentParameters_intersection D k hk b3 b4 b6 h3 h4 h6 hp
          hy.symm
      · refine ⟨y', ?_⟩
        simpa only [← Scheme.Hom.comp_apply, laurentConicComponentSecondAffine_torus]
          using hy
    · refine ⟨x', ?_⟩
      rw [← Scheme.Hom.comp_apply, laurentConicComponentFirstAffine_torus]
  · rintro z ⟨t, rfl⟩
    constructor
    · refine ⟨ProjectiveLine.scaledOverlapLeft K ((hc).unit)⁻¹ t, ?_⟩
      rw [← Scheme.Hom.comp_apply, laurentConicComponentFirstAffine_torus]
    · refine ⟨ProjectiveLine.overlapRight K t, ?_⟩
      rw [← Scheme.Hom.comp_apply, laurentConicComponentSecondAffine_torus]

/-- The ordered full Laurent maps give the actual scheme-theoretic affine intersection. -/
theorem laurentConicComponentAffine_isPullback :
    IsPullback (ProjectiveLine.scaledOverlapLeft K ((hc).unit)⁻¹)
      (ProjectiveLine.overlapRight K) f g := by
  apply IsOpenImmersion.isPullback _ _ _ _
    (laurentConicComponentAffine_transition D k hk b3 b4 b6 h3 h4 h6 hp).symm
  apply TopologicalSpace.Opens.ext
  change g ⁻¹' Set.range f = Set.range (ProjectiveLine.overlapRight K)
  ext y
  constructor
  · intro hy
    have hr : g y ∈ Set.range r := by
      rw [← laurentConicComponentAffine_intersection]
      exact ⟨hy, ⟨y, rfl⟩⟩
    obtain ⟨z, hz⟩ := hr
    refine ⟨z, (g).isOpenEmbedding.injective ?_⟩
    simpa only [← Scheme.Hom.comp_apply, laurentConicComponentSecondAffine_torus] using hz
  · rintro ⟨z, rfl⟩
    refine ⟨ProjectiveLine.scaledOverlapLeft K ((hc).unit)⁻¹ z, ?_⟩
    simp only [← Scheme.Hom.comp_apply, laurentConicComponentFirstAffine_torus,
      laurentConicComponentSecondAffine_torus]

end FLT.Mazur.WeierstrassSuccessiveX
