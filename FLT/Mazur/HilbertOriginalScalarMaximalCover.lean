/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertMaximalScalarCompleteChart

/-!
# Whole complete charts above every actual original scalar character

Maximize the size of actual frames while retaining the original scalar map.
Place a maximizing frame in a stable affine chart. Every full invariant prime
of that chart over the same scalar prime is complete, by strict frame growth.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart.AffineRestriction
open CartierAbel SchemePicard FCurve EquivalenceRelationNormalizedFrames
open FiniteGroupRestriction SchemeFiniteGroupQuotient SchemeOpenEnvelope
open RelativeRelationOrbit SchemeScalarPrincipalNeighborhood
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R] {X : Scheme}
  (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  (d : ℕ) (V : Over (Spec (.of R))) [IsAffine V.left] [Etale V.hom]
  (c : (relativeFppfSheaf f).obj.obj (op V))
  {A : Over (Spec (.of R))} [IsAffine A.left]
  (k : A ⟶ variableHilbertTest f d V) [IsOpenImmersion k.left]
local notation "p" => Over.Hom.left (fst f hL d V c k)
local notation "q" => Over.Hom.left (snd f hL d V c k)
local notation "e" => fullRelationSchemeEquivalence f hL d V c k
attribute [local irreducible] relation fst snd equivalence

local notation "eo" => equivalence f hL d V c k
variable (W : TopologicalSpace.Opens (Orbit (equivalence f hL d V c k)))
set_option quotPrecheck false
local notation "E" => (pullOpen eo W).val
local notation "Ω" => (invariantSheaf eo).obj.obj (op W)
local notation "s" => orbitScalarCoordinates eo W

attribute [local irreducible] invariantSheaf orbitScalarCoordinates
  EquivalenceRelationNormalizedFrames.source first completeInterior Complete
  scalarMorphism finiteTargetOpen

local notation "K" P => scalarResidueClosure P
local notation "t" P => Spec.map (CommRingCat.ofHom (algebraMap Ω (K P)))
attribute [local irreducible] scalarResidueClosureField scalarResidueClosureAlgebra

/-- An original geometric endpoint constructs a chart with a whole complete scalar fiber. -/
theorem exists_original_wholeScalar_chart (P : PrimeSpectrum Ω)
    (b : Spec (.of (K P)) ⟶ (E).toScheme) (hb : b ≫ scalarMorphism s = t P) :
    ∃ (n : ℕ) (o : Fin n)
      (U : (normalizedFullRelationFrames f hL d V c k n o).Opens)
      (hU : ∀ g : Equiv.Perm (Fin n),
        (normalizedFullRelationAction f hL d V c k n o g).hom ⁻¹ᵁ U = U)
      (hUW : U ≤ normalizedFullRelationFirst f hL d V c k n o ⁻¹ᵁ E)
      (ha : IsAffineOpen U),
      let _ : IsAffine U.toScheme := ha
      P ∈ wholeCompleteScalarLocus e (Fin n) o U hU
        (normalizedOriginalScalarMap f hL d V c k n o W U hU hUW) := by
  let _ := selectedAffineHilbertSource_isNoetherian f d V k
  obtain ⟨n, hn, hmax⟩ := exists_maximal_scalarFrameSize («p» := p) («q» := q) E s (t P)
    (scalarFrameSizes_nonempty e E s (t P) b hb)
  rw [scalarFrameSizes] at hn
  obtain ⟨o, u, a, hu, ha⟩ := hn
  obtain ⟨U, hU, hUW, z, hUa, hz, hs⟩ :=
    exists_original_scalar_frame_chart f hL d V c k W a n o u hu
  let _ : IsAffine U.toScheme := hUa
  refine ⟨n, o, U, hU, hUW, hUa, ?_⟩
  apply original_wholeScalar_of_maximal_frameSize f hL d V c k W n o U hU hUW P hmax
  let ρ := restrictedAction (normalizedFullRelationAction f hL d V c k n o) U hU
  refine ⟨quotientMap ρ (z default), ?_⟩
  have ht := congrArg (fun g : Spec (.of (K P)) ⟶ Spec (.of Ω) ↦ g default)
    (hs.trans ha)
  rw [scalarMorphism_through_quotient] at ht
  exact ht.trans (scalarResidueClosure_center P)

end FLT.Mazur.HilbertChart.AffineRestriction
