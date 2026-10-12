/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSuccessiveShearTerminalAffineCover
public import FLT.Mazur.WeierstrassModificationXConicBoundaryIntersection

/-!
# The complete intersection of the two terminal affine charts

No extra points occur in the intersection: it is exactly the entire
original Laurent chart, with the ordered scaled reciprocal coordinates.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
open scoped Polynomial LaurentPolynomial
namespace FLT.Mazur.WeierstrassSuccessiveShearTerminal
open WeierstrassModificationX WeierstrassSuccessiveX WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option quotPrecheck false
universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R) (π : R)
  (k : ℕ) (b3 b4 b6 : R) (S : Type u) [Field S] [Algebra R S] (ρ : S)
  (hs : algebraMap R S (π ^ k) = 0) (hp : algebraMap R S π = 0)
  (h3 : algebraMap R S b3 = 0) (h4 : algebraMap R S b4 = 0)
  (hr : ρ ^ 2 + algebraMap R S W.a₁ * ρ - algebraMap R S W.a₂ = 0)
  (hc : IsUnit (algebraMap R S b6)) (u : Sˣ)
  (hu : (u : S) = (rootShearCurve (W.map (algebraMap R S)) ρ).a₁)
local notation "U" => rootShearCurve (W.map (algebraMap R S)) ρ
local notation "K" => S
local notation "a" => WeierstrassCurve.a₁ U
local notation "c" => algebraMap R S b6
local notation "ha" => Eq.mp (congrArg IsUnit hu) (Units.isUnit u)
local notation "P" => laurentConicComponent W π k b3 b4 b6 S ρ hs hp h3 h4 hr hc u hu
local notation "l" => laurentConicComponentConic W π k b3 b4 b6 S ρ hs hp h3 h4 hr hc u hu
local notation "r" => laurentConicComponentTorus W π k b3 b4 b6 S ρ hs hp h3 h4 hr hc u hu
local notation "j" => PrincipalOpenTransport.inclusion (conicParameterPolynomial c)
local notation "f" => laurentConicComponentFirstAffine W π k b3 b4 b6 S ρ hs hp h3 h4 hr hc u hu
local notation "g" => laurentConicComponentSecondAffine W π k b3 b4 b6 S ρ hs hp h3 h4 hr hc u hu

local notation "i" => Spec.map (CommRingCat.ofHom
  (algebraMap (ConicCoordinate a c) (ConicIncidenceOpen a c)))
local notation "ψ" => tensorShearTerminalLaurentConicMap W π k b3 b4 b6 S ρ hs hp h3 h4 hr hc u hu
local notation "s" => Spec.map (CommRingCat.ofHom (AlgHom.toRingHom ψ))
local notation "q₁" => laurentConicComponentFirstParameter W π k b3 b4 b6 S ρ hs hp h3 h4 hr hc u hu
local notation "q₂" => laurentConicComponentSecondParameter W π k b3 b4 b6 S ρ hs hp h3 h4 hr hc
  u hu

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
    · rcases terminalSecondAffine_cover b6 S y with ⟨y', rfl⟩ | ⟨y', rfl⟩
      · change g (j y') = f (j x') at hy
        change f (j x') ∈ Set.range r
        simp only [← Scheme.Hom.comp_apply, laurentConicComponentFirstAffine_parameter,
          laurentConicComponentSecondAffine_parameter] at hy ⊢
        rw [← hy]
        exact laurentConicComponentParameters_intersection W π k b3 b4 b6 S ρ hs hp h3 h4 hr hc u hu
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
    (laurentConicComponentAffine_transition W π k b3 b4 b6 S ρ hs hp h3 h4 hr hc u hu).symm
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

end FLT.Mazur.WeierstrassSuccessiveShearTerminal
