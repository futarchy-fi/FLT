/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertCompleteChartScalarCover
public import FLT.Mazur.EquivalenceRelationCompleteNeighborhoodCharacters
public import FLT.Mazur.SchemeFiniteGroupQuotientOrbits

/-!
# Complete original representatives at every scalar character

The proved comparison on a complete chart's own orbit image turns an original
scalar character into its unique full invariant character. Lifting retains the
original field, frame size and scalar character. Equality of scalar values now
really determines an original relation arrow, by the proved comparison.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart.AffineRestriction
open CartierAbel SchemePicard FCurve EquivalenceRelationNormalizedFrames
open RelativeRelationOrbit InvariantOpenRelationDiagram
open FiniteGroupRestriction SchemeFiniteGroupQuotient
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R] {X : Scheme}
  (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  (d : ℕ) (V : Over (Spec (.of R))) [IsAffine V.left] [Etale V.hom]
  (c : (relativeFppfSheaf f).obj.obj (op V))
  {A : Over (Spec (.of R))} [IsAffine A.left]
  (k : A ⟶ variableHilbertTest f d V) [IsOpenImmersion k.left]
local notation "p" => Over.Hom.left (AffineRestriction.fst f hL d V c k)
local notation "q" => Over.Hom.left (AffineRestriction.snd f hL d V c k)
local notation "e" => fullRelationSchemeEquivalence f hL d V c k
local notation "eo" => equivalence f hL d V c k
variable (n : ℕ) (o : Fin n)
  (U : (normalizedFullRelationFrames f hL d V c k n o).Opens)
  (hU : ∀ g : Equiv.Perm (Fin n),
    (normalizedFullRelationAction f hL d V c k n o g).hom ⁻¹ᵁ U = U)
attribute [local irreducible] relation AffineRestriction.fst AffineRestriction.snd equivalence
  EquivalenceRelationNormalizedFrames.source relativeFppfSheaf AmpleLineBundle
local notation "j" => U.ι ≫ normalizedFullRelationFirst f hL d V c k n o
set_option quotPrecheck false
local notation "O" => orbitImageOpen eo (q).isOpenMap (etaleSourceImage j)
local notation "E" => (pullOpen eo O).val
local notation "Ω" => (invariantSheaf eo).obj.obj (op O)
local notation "τ" => normalizedFullRelationAction f hL d V c k n o
local notation "Sinv" => invariantCoordinates (restrictedAction τ U hU)

local notation "hUO" => normalizedChart_over_orbitImage f hL d V c k n o U
local notation "σ" => normalizedOriginalScalarMap f hL d V c k n o O U hU hUO
local notation "ρ" => restrictedAction τ U hU
local notation "σ₀" => invariantScalarCoordinates ρ σ
open SchemeScalarPrincipalNeighborhood

variable [IsAffine U.toScheme]

/-- On this domain, a scalar fiber is one actual moving-frame orbit. -/
theorem completeChart_scalar_fiber_iff_orbit
    (hc : ∀ y ∈ U, y ∈ completePointLocus («p» := p) («q» := q) (Fin n) o)
    (x y : U.toScheme) :
    scalarMorphism σ₀ x = scalarMorphism σ₀ y ↔
      ∃ g : Equiv.Perm (Fin n), y = (ρ g).hom x := by
  rw [completeChart_scalarMorphism_factor]
  let _ := completeChart_scalarSpec_isIso f hL d V c k n o U hU hc
  change Spec.map (CommRingCat.ofHom σ) (quotientMap ρ x) =
    Spec.map (CommRingCat.ofHom σ) (quotientMap ρ y) ↔ _
  exact (Spec.map (CommRingCat.ofHom σ)).homeomorph.injective.eq_iff.trans
    (quotientMap_eq_iff_orbit ρ x y)

variable {K : Type} [Field K]
local notation "u" w => sourceCharacterMap (X := U.toScheme) w ≫ U.ι

omit [IsAffine U.toScheme] in
/-- Scalar agreement determines all invariants through the actual bijective scalar pullback. -/
theorem completeChart_scalar_characters_determine_invariants
    (hc : ∀ y ∈ U, y ∈ completePointLocus («p» := p) («q» := q) (Fin n) o)
    (v w : Γ(U.toScheme, ⊤) →+* K) (h : v.comp σ₀ = w.comp σ₀) :
    ∀ t : Sinv, v t.val = w t.val := by
  intro t
  obtain ⟨r, rfl⟩ :=
    (normalizedOriginalScalarMap_orbitImage_bijective f hL d V c k n o U hU hc).surjective t
  exact congrArg (fun a : Ω →+* K ↦ a r) h

/-- Two original scalar lifts have a unique full original relation arrow, over their given field. -/
theorem completeChart_scalar_characters_original_arrow
    (hc : ∀ y ∈ U, y ∈ completePointLocus («p» := p) («q» := q) (Fin n) o)
    (v w : Γ(U.toScheme, ⊤) →+* K) (h : v.comp σ₀ = w.comp σ₀) :
    ∃! a : Spec (.of K) ⟶ (relation f hL d V c k).left,
      a ≫ p = (u v) ≫ normalizedFullRelationFirst f hL d V c k n o ∧
      a ≫ q = (u w) ≫ normalizedFullRelationFirst f hL d V c k n o := by
  exact invariant_character_original_arrow e (Fin n) o U hU v w
    (completeChart_scalar_characters_determine_invariants f hL d V c k n o U hU hc v w h)

/-- Every original scalar character has a complete lift, with its entire residue map unchanged. -/
theorem completeChart_originalScalar_character_lift [IsAlgClosed K]
    (hc : ∀ y ∈ U, y ∈ completePointLocus («p» := p) («q» := q) (Fin n) o)
    (χ : Ω →+* K) :
    ∃ w : Γ(U.toScheme, ⊤) →+* K,
      w.comp σ₀ = χ ∧ Complete (Fin n) o (u w) := by
  let comparison := completeChartScalarIso f hL d V c k n o U hU hc
  obtain ⟨w, hw, hC⟩ := completeOpen_character_lift e (Fin n) o U hU
    (fun _ hy ↦ hc _ hy) (χ.comp comparison.symm.toRingHom)
  refine ⟨w, ?_, hC⟩
  ext r
  change w (σ r).val = χ r
  rw [hw]
  exact congrArg χ (comparison.symm_apply_apply r)

end FLT.Mazur.HilbertChart.AffineRestriction
