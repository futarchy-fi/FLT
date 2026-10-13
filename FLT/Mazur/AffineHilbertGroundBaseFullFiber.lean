/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineHilbertGroundBaseEnvelope
public import FLT.Mazur.AffineHilbertFiniteFiberPrincipal

/-!
# Retaining full fibers through genuine ground-base changes

The Cartesian original envelope transports every previously full fiber,
including its independent residue branches. Finite new translations turn
these transported fibers into open full-envelope domains and give actual
principal affine restrictions retaining the point in their new interiors.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart.AffineRestriction
open FCurve CartierAbel SchemePicard SchemeOpenEnvelope
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {R R' : Type} [CommRing R] [CommRing R']
  [Algebra.FiniteType ℤ R] [Algebra.FiniteType ℤ R']
  {X : Scheme} (f : X ⟶ Spec (.of R)) (a : Spec (.of R') ⟶ Spec (.of R))
  [IsProper f] [Flat f] [GeometricallyIntegral f] [SmoothOfRelativeDimension 1 f]
  {L : X.Modules} (hL : AmpleLineBundle L) (d : ℕ)
  (V : Over (Spec (.of R))) (W : Over (Spec (.of R')))
  (t : (Over.map a).obj W ⟶ V) (c : (relativeFppfSheaf f).obj.obj (op V))
local notation "q" => Limits.pullback.snd f a
local instance : SmoothOfRelativeDimension 1 q :=
  MorphismProperty.pullback_snd _ _ inferInstance
variable {A : Over (Spec (.of R))} (k : A ⟶ variableHilbertTest f d V)
local notation "B" => groundBaseSource f a hL d V W t k
local notation "u" => groundBaseSourceMap f a hL d V W t k
local notation "l" => groundBaseSourceChart f a hL d V W t k
local notation "h'" => fixedBaseAmple f a hL
local notation "c'" => fixedBaseTranslationClass f a V W t c
local notation "p" => fst f hL d V c k
local notation "s" => snd f hL d V c k
local notation "p'" => fst q h' d W c' l
local notation "s'" => snd q h' d W c' l
local notation "j" => toEnvelope f hL d V c k
local notation "j'" => toEnvelope q h' d W c' l
local notation "v" => fixedBaseRelationMap f a hL d V W t c k l u
  (groundBaseSource_square f a hL d V W t k)
local notation "m" => fixedBaseEnvelopeMap a V W t u
variable [IsOpenImmersion k.left]
local notation "π" => Over.Hom.left (prod.fst : prod A V ⟶ A)
local notation "π'" => Over.Hom.left (prod.fst : prod B W ⟶ B)

/-- Fullness survives the actual changed ground base, source and independent translation. -/
theorem groundBaseSource_fullFiber_mono :
    (u).left ⁻¹' fullEnvelopeLocus f hL d V c k ⊆
      fullEnvelopeLocus q h' d W c' l := by
  intro x hx
  apply (mem_fullFiberLocus π' (j').left.opensRange x).mpr
  intro y hy
  have hp : π ((m).left y) = (u).left x := by
    change ((m).left ≫ π) y = _
    rw [← Over.comp_left, fixedBaseEnvelopeMap_fst]
    change (u).left (π' y) = (u).left x
    rw [hy]
  obtain ⟨z, hz⟩ := (mem_fullFiberLocus π (j).left.opensRange _).mp hx _ hp
  obtain ⟨w, _, hw⟩ := Scheme.exists_preimage_of_isPullback
    (groundBaseEnvelope_isPullback f a hL d V W t c k) z y hz
  exact ⟨w, hw⟩

/-- The preimage of the original full-fiber interior lies in the new interior. -/
theorem groundBaseSource_fullInterior_mono :
    (u).left ⁻¹ᵁ fullEnvelopeInterior f hL d V c k ≤
      fullEnvelopeInterior q h' d W c' l := by
  apply interior_maximal _ ((u).left.continuous.isOpen_preimage _
    (fullEnvelopeInterior f hL d V c k).isOpen)
  intro x hx
  apply groundBaseSource_fullFiber_mono f a hL d V W t c k
  change (u).left x ∈ fullEnvelopeLocus f hL d V c k
  exact interior_subset hx

/-- A finite new translation makes each transported full fiber an actual open-domain point. -/
theorem groundBaseSource_mem_interior_of_finite [IsFinite W.hom]
    (x : (B).left) (hx : (u).left x ∈ fullEnvelopeLocus f hL d V c k) :
    x ∈ fullEnvelopeInterior q h' d W c' l := by
  exact (Set.ext_iff.mp (fullEnvelopeLocus_eq_interior_of_finite q h' d W c' l) x).mp
    (groundBaseSource_fullFiber_mono f a hL d V W t c k hx)

/-- The new finite translation yields an affine principal source with a retained interior point. -/
theorem groundBaseSource_exists_finite_principal [IsFinite W.hom] [Etale W.hom]
    [IsAffine A.left] [IsAffine V.left] [IsAffine W.left]
    (x : (B).left) (hx : (u).left x ∈ fullEnvelopeLocus f hL d V c k) :
    ∃ (r : Γ((B).left, ⊤)) (hr : x ∈ (B).left.basicOpen r),
      (B).left.basicOpen r ≤ fullEnvelopeInterior q h' d W c' l ∧
      (⟨x, hr⟩ : ((B).left.basicOpen r).toScheme) ∈
        fullEnvelopeInterior q h' d W c' (orbitPrincipalChart q d W l r) :=
  exists_finite_fullFiber_principal_interior q h' d W c' l x
    (groundBaseSource_fullFiber_mono f a hL d V W t c k hx)

end FLT.Mazur.HilbertChart.AffineRestriction
