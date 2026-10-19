/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertCompleteChartOriginalSections
public import FLT.Mazur.HilbertSubframeOriginalScalars
public import FLT.Mazur.RelativeRelationEtaleOrbitImageMap
public import FLT.Mazur.SchemeFiniteGroupFreeFlat
public import FLT.Mazur.SchemeOriginalScalarOpenCorrections

/-!
# The original scalar ring on a complete chart's own orbit image

Complete chart coefficients descend uniquely to original orbit sections.
The resulting isomorphism is the existing original scalar map, with its
actual geometric pullback. The domain is the chart's own orbit image;
no such isomorphism is claimed for an arbitrary larger prescribed domain.
The free quotient then proves source flatness over these actual original scalars.
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

/-- The original chart lands in the original source open of its own orbit image. -/
theorem normalizedChart_over_orbitImage :
    U ≤ normalizedFullRelationFirst f hL d V c k n o ⁻¹ᵁ E := by
  intro x hx
  exact le_saturateOpen eo (q).isOpenMap (etaleSourceImage j) ⟨⟨x, hx⟩, rfl⟩

local notation "hUO" => normalizedChart_over_orbitImage f hL d V c k n o U
local notation "σ" => normalizedOriginalScalarMap f hL d V c k n o O U hU hUO

/-- The existing scalar pullback is precisely the established original section comparison. -/
theorem normalizedOriginalScalarMap_orbitImage_val (b : Ω) :
    (σ b).val = (etaleSourceFunctionEquiv eo (q).isOpenMap j b).val := by
  have he : (normalizedFullRelationFirst f hL d V c k n o).resLE E U hUO =
      etaleOrbitImageMap eo (q).isOpenMap j := by
    apply (cancel_mono (E).ι).mp
    rw [Scheme.Hom.resLE_comp_ι, etaleOrbitImageMap_ι]
  rw [normalizedOriginalScalarMap_val, he, etaleOrbitImageMap_appTop]

/-- Complete support makes the actual original scalar map bijective on its own orbit image. -/
theorem normalizedOriginalScalarMap_orbitImage_bijective
    (hc : ∀ y ∈ U, y ∈ completePointLocus («p» := p) («q» := q) (Fin n) o) :
    Function.Bijective σ := by
  constructor
  · intro a b hab
    apply (etaleSourceFunctionEquiv eo (q).isOpenMap j).injective
    apply Subtype.ext
    rw [← normalizedOriginalScalarMap_orbitImage_val,
      ← normalizedOriginalScalarMap_orbitImage_val, hab]
  · intro t
    obtain ⟨b, hb, _⟩ := completeChart_original_section_existsUnique
      f hL d V c k n o U hU hc t
    refine ⟨b, Subtype.ext ?_⟩
    rw [normalizedOriginalScalarMap_orbitImage_val]
    exact hb

/-- Original orbit scalars and all chart invariants are identified by their original pullback. -/
def completeChartScalarIso
    (hc : ∀ y ∈ U, y ∈ completePointLocus («p» := p) («q» := q) (Fin n) o) :
    Ω ≃+* Sinv := RingEquiv.ofBijective σ
      (normalizedOriginalScalarMap_orbitImage_bijective f hL d V c k n o U hU hc)

/-- Source flatness is proved over the original scalars of the complete chart's own orbit image. -/
theorem completeChart_originalSource_flat [IsAffine U.toScheme]
    (hc : ∀ y ∈ U, y ∈ completePointLocus («p» := p) («q» := q) (Fin n) o) :
    (invariantScalarCoordinates (restrictedAction τ U hU) σ).Flat := by
  let ρ := restrictedAction τ U hU
  have hfree : ∀ (K : Type) [Field K] (a : Spec (.of K) ⟶ U.toScheme)
      (g : Equiv.Perm (Fin n)), a ≫ (ρ g).hom = a → g = 1 :=
    restrictedAction_free τ U hU (fun _ _ a g hg ↦ action_free e (Fin n) o a g hg)
  let _ := SchemeCoordinateAction.coordinateAction ρ
  let _ := FiniteGroupQuotient.invariant_module_projective (Equiv.Perm (Fin n))
    (coordinate_fixedPointIdeal_eq_top ρ hfree)
  have hi : (FiniteGroupQuotient.inclusion (Equiv.Perm (Fin n)) Γ(U.toScheme, ⊤)).Flat :=
    RingHom.flat_algebraMap_iff.mpr inferInstance
  exact (RingHom.Flat.of_bijective
    (normalizedOriginalScalarMap_orbitImage_bijective f hL d V c k n o U hU hc)).comp hi

end FLT.Mazur.HilbertChart.AffineRestriction
