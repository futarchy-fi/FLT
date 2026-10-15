/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineHilbertPrincipalInvariantSupports
public import FLT.Mazur.AffineHilbertNestedInteriorImage
public import FLT.Mazur.SchemeRelationInvariantFunctorial

/-!
# Transporting admissibility back to the original invariant ring

An invariant principal denominator need not be admissible. Any admissible
coefficient constructed on that principal chart nevertheless gives an
ORIGINAL admissible coefficient with exactly the same nonvanishing support.
Conversely original admissibility restricts to the full principal relation.
Thus these recomputations preserve pointwise original admissible coverage.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart.AffineRestriction
open CartierAbel SchemePicard FCurve SchemeEffectiveEpiSections
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] relation fst snd
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R] {X : Scheme}
  (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  (d : ℕ) (V : Over (Spec (.of R))) [Etale V.hom] [IsAffine V.left]
  (c : (relativeFppfSheaf f).obj.obj (op V))
  {A : Over (Spec (.of R))} [IsAffine A.left]
  (k : A ⟶ variableHilbertTest f d V) [IsOpenImmersion k.left]
local notation "p" => Over.Hom.left (fst f hL d V c k)
local notation "q" => Over.Hom.left (snd f hL d V c k)
local notation "C" => compatibleFunctions
  (Over.Hom.left (fst f hL d V c k)) (Over.Hom.left (snd f hL d V c k))
variable (s : compatibleFunctions (fst f hL d V c k).left (snd f hL d V c k).left)
local notation "B" => invariantPrincipalSource f hL d V c k s
local notation "u" => invariantPrincipalSourceMap f hL d V c k s
local notation "l" => invariantPrincipalChart f hL d V c k s
local instance principalTransport_open : IsOpenImmersion (u).left :=
  inferInstanceAs (IsOpenImmersion (A.left.basicOpen s.val).ι)
local notation "C'" => compatibleFunctions
  (Over.Hom.left (fst f hL d V c (invariantPrincipalChart f hL d V c k s)))
  (Over.Hom.left (snd f hL d V c (invariantPrincipalChart f hL d V c k s)))

/-- Construct an old admissible coefficient from a new one, with its exact original support. -/
theorem principalAdmissible_exists_original (z : C')
    (hz : z ∈ invariantEnvelopeDenominators f hL d V c l) :
    ∃ a : C, a ∈ invariantEnvelopeDenominators f hL d V c k ∧
      A.left.basicOpen a.val = (u).left ''ᵁ (B).left.basicOpen z.val := by
  obtain ⟨a, ha, _⟩ := principalInvariant_exists_original_support f hL d V c k s z
  refine ⟨a, ?_, ha⟩
  rw [invariantDenominator_iff_fullEnvelopeInterior, ha]
  have h : (u).left ''ᵁ fullEnvelopeInterior f hL d V c l ≤
      fullEnvelopeInterior f hL d V c k := by
    unfold invariantPrincipalChart
    exact nested_fullEnvelopeInterior_image_le f hL d V c k u
  exact ((u).left.image_mono
    ((invariantDenominator_iff_fullEnvelopeInterior f hL d V c l z).mp hz)).trans h

/-- Pull original functions through the actual full recomputed relation. -/
def principalInvariantRestriction : C →+* C' := by
  unfold invariantPrincipalChart
  exact SchemeRelationInvariantSpectrum.relationPullback p q
    (fst f hL d V c (u ≫ k)).left (snd f hL d V c (u ≫ k)).left (u).left
    (nestedToFullRelation f hL d V c k u).left
    (congrArg Over.Hom.left (nestedToFullRelation_fst f hL d V c k u))
    (congrArg Over.Hom.left (nestedToFullRelation_snd f hL d V c k u))

omit [Etale V.hom] [IsAffine V.left] [IsAffine A.left] [IsOpenImmersion k.left] in
/-- The transported function is literally the original structure-sheaf pullback. -/
theorem principalInvariantRestriction_val (a : C) :
    (principalInvariantRestriction f hL d V c k s a).val = (u).left.appTop a.val := rfl

omit [Etale V.hom] [IsAffine V.left] [IsAffine A.left] in
/-- The full-envelope interior commutes with an original invariant principal restriction. -/
theorem principal_fullEnvelopeInterior_eq :
    fullEnvelopeInterior f hL d V c l =
      (u).left ⁻¹ᵁ fullEnvelopeInterior f hL d V c k := by
  unfold invariantPrincipalChart
  apply nested_fullEnvelopeInterior_eq f hL d V c k u
  change p ⁻¹ᵁ (A.left.basicOpen s.val).ι.opensRange =
    q ⁻¹ᵁ (A.left.basicOpen s.val).ι.opensRange
  rw [Scheme.Opens.opensRange_ι]
  exact compatibleFunctions_basicOpen p q s

omit [Etale V.hom] [IsAffine V.left] [IsAffine A.left] in
/-- Every old admissible coefficient remains admissible on the full new relation. -/
theorem principalInvariantRestriction_admissible (a : C)
    (ha : a ∈ invariantEnvelopeDenominators f hL d V c k) :
    principalInvariantRestriction f hL d V c k s a ∈
      invariantEnvelopeDenominators f hL d V c l := by
  rw [invariantDenominator_iff_fullEnvelopeInterior, principalInvariantRestriction_val,
    ← Scheme.preimage_basicOpen_top, principal_fullEnvelopeInterior_eq]
  exact fun _ hx ↦ (invariantDenominator_iff_fullEnvelopeInterior f hL d V c k a).mp ha hx

/-- Recomputed admissible coverage is exactly original admissible coverage at the same point. -/
theorem principal_admissible_coverage_iff (x : (B).left) :
    (∃ z : C', z ∈ invariantEnvelopeDenominators f hL d V c l ∧
      x ∈ (B).left.basicOpen z.val) ↔
    ∃ a : C, a ∈ invariantEnvelopeDenominators f hL d V c k ∧
      (u).left x ∈ A.left.basicOpen a.val := by
  constructor
  · rintro ⟨z, hz, hx⟩
    obtain ⟨a, ha, he⟩ := principalAdmissible_exists_original f hL d V c k s z hz
    refine ⟨a, ha, ?_⟩
    rw [he]
    exact ⟨x, hx, rfl⟩
  · rintro ⟨a, ha, hx⟩
    refine ⟨principalInvariantRestriction f hL d V c k s a,
      principalInvariantRestriction_admissible f hL d V c k s a ha, ?_⟩
    rw [principalInvariantRestriction_val, ← Scheme.preimage_basicOpen_top]
    exact hx

end FLT.Mazur.HilbertChart.AffineRestriction
