/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertUniformPrincipalErrorSupport

/-!
# Finite original geometric scalars generating the boundary source ideal

Noetherianity of the actual boundary source ring extracts finitely many of
the original geometric scalars. They generate the same source ideal and
detect exactly the same primes. This is source ideal finiteness, not finite
generation of the invariant boundary ring over the invariant scalar ring.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart.AffineRestriction
open CartierAbel SchemePicard FCurve SchemeOpenEnvelope
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R] {X : Scheme}
  (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  (d : ℕ) (V : Over (Spec (.of R))) [Etale V.hom]
  (c : (relativeFppfSheaf f).obj.obj (op V))
  {A : Over (Spec (.of R))} [IsAffine A.left]
  (k : A ⟶ variableHilbertTest f d V) [IsOpenImmersion k.left]
local notation "π" => Over.Hom.left (prod.fst : prod A V ⟶ A)
local notation "O" => Scheme.Hom.opensRange (Over.Hom.left (toEnvelope f hL d V c k))
local notation "B" => originalBoundarySource f hL d V c k
local notation "i" => originalBoundarySourceMap f hL d V c k
local notation "D" => relation f hL d V c k
local notation "p" => fst f hL d V c k
local notation "q" => snd f hL d V c k

local notation "C" => originalClosedRelation f hL d V c k
local notation "r" => originalClosedFst f hL d V c k
local notation "s" => originalClosedSnd f hL d V c k
local notation "z" => originalClosedArrow f hL d V c k

open RelativeRelationOrbit
local notation "e" => equivalence f hL d V c k
local notation "ec" => originalClosedEquivalence f hL d V c k

attribute [local irreducible] originalBoundarySource originalBoundarySourceMap
  originalClosedRelation originalClosedFst originalClosedSnd originalClosedArrow
  originalClosedEquivalence relation fst snd equivalence

local notation "m" => originalClosedInvariantMap f hL d V c k

set_option quotPrecheck false
variable (W : TopologicalSpace.Opens (Orbit (equivalence f hL d V c k)))
local notation "Wc" => (TopologicalSpace.Opens.map (m).base).obj W
local notation "Q" => (sourceSheaf e).obj.obj (op W)
local notation "T" => (sourceSheaf ec).obj.obj (op Wc)

local notation "D₀" => (invariantSheaf ec).obj.obj (op Wc)
local notation "r₀" => originalAmbientBoundaryRestriction f hL d V c k W
attribute [local irreducible] originalAmbientBoundaryRestriction
variable (hW : IsAffineOpen (pullOpen (equivalence f hL d V c k) W).val)

local notation "n" => originalAmbientBoundaryFrameSize f hL d V c k W hW
local notation "p₀" => ((firstRestriction e).hom.app (op W)).hom
local notation "q₀" => ((secondRestriction e).hom.app (op W)).hom
local notation "ρ" => originalClosedSectionPullback f hL d V c k W
attribute [local irreducible] originalAmbientBoundaryFrame originalAmbientBoundaryFrameSize
  originalAmbientBoundaryLift

local notation "ι₀" => ((invariantInclusion e).hom.app (op W)).hom
local notation "ιc" => ((invariantInclusion ec).hom.app (op Wc)).hom

open OrbitBoundaryAtlas.FiniteAtlas
attribute [local instance] originalBoundarySectionAlgebra
attribute [local irreducible] originalBoundaryLiftErrorClass
  originalBoundaryExtendedCokernelAddCommGroup originalBoundaryExtendedCokernelModule
local notation "Ω" => (invariantSheaf e).obj.obj (op W)
local notation "κ" => (ιc).comp ρ

attribute [local instance] originalAmbientSourceAlgebra originalAmbientRelationAlgebra
  originalAmbientBoundaryAlgebra
attribute [local irreducible] relationSheaf originalAmbientLocalizedCorrection

variable [IsAffine V.left]
attribute [local irreducible] relativeFppfSheaf AmpleLineBundle
  EquivalenceRelationNormalizedFrames.source
  OrbitBoundaryAtlas.uniformPrincipalScalars

local notation "S" => OrbitBoundaryAtlas.uniformPrincipalScalars f hL d V c k W
local notation "J" => OrbitBoundaryAtlas.uniformPrincipalIdeal f hL d V c k W

local notation "Jb" => uniformPrincipalBoundaryIdeal f hL d V c k W

/-- The constructed boundary ideal is the span of the actual images of geometric scalars. -/
theorem uniformPrincipalBoundaryIdeal_eq_span : Jb = Ideal.span (κ '' S) := by
  unfold uniformPrincipalBoundaryIdeal OrbitBoundaryAtlas.uniformPrincipalIdeal
  exact Ideal.map_span κ _

include hW in
/-- A finite family of original geometric scalars generates the whole actual source ideal. -/
theorem uniformPrincipalBoundaryIdeal_finite_generators :
    ∃ indices : Finset S, Ideal.span
      ((fun a : S ↦ κ a.val) '' (indices : Set S)) = Jb := by
  classical
  let _ := originalAmbientBoundary_noetherian f hL d V c k W hW
  have hf : (Ideal.span (κ '' S)).FG := IsNoetherian.noetherian _
  obtain ⟨b, hb, he⟩ := (Submodule.fg_span_iff_fg_span_finset_subset (κ '' S)).mp hf
  change Ideal.span (κ '' S) = Ideal.span (b : Set T) at he
  choose a ha hae using fun x : b ↦ hb x.property
  let j : b → S := fun x ↦ ⟨a x, ha x⟩
  refine ⟨Finset.univ.image j, ?_⟩
  rw [uniformPrincipalBoundaryIdeal_eq_span, he]
  congr 1
  ext x
  constructor
  · rintro ⟨v, hv, rfl⟩
    obtain ⟨y, _, rfl⟩ := Finset.mem_image.mp hv
    change κ (a y) ∈ b
    rw [hae y]
    exact y.property
  · intro hx
    refine ⟨j ⟨x, hx⟩, Finset.mem_image.mpr ⟨⟨x, hx⟩, Finset.mem_univ _, rfl⟩, ?_⟩
    exact hae ⟨x, hx⟩

include hW in
/-- A finite original scalar family detects all primes outside the constructed closed support. -/
theorem uniformPrincipalBoundaryIdeal_finite_prime_test :
    ∃ indices : Finset S, ∀ P : Ideal T,
      (¬ Jb ≤ P) ↔ ∃ a ∈ indices, κ a.val ∉ P := by
  obtain ⟨indices, hi⟩ := uniformPrincipalBoundaryIdeal_finite_generators f hL d V c k W hW
  refine ⟨indices, fun P ↦ ?_⟩
  rw [← hi, Ideal.span_le]
  constructor
  · intro h
    by_contra hn
    apply h
    rintro _ ⟨a, ha, rfl⟩
    by_contra hp
    exact hn ⟨a, ha, hp⟩
  · rintro ⟨a, ha, hp⟩ h
    exact hp (h ⟨a, ha, rfl⟩)

end FLT.Mazur.HilbertChart.AffineRestriction
