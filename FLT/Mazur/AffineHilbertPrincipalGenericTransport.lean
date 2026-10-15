/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineHilbertPrincipalAdmissibleTransport
public import FLT.Mazur.AffineHilbertGenericEnvelopeCriterion

/-!
# Generic-envelope certificates survive recomputation on invariant principals

For a nonempty invariant principal of an integral original source, the old
and recomputed denominator ideals are nonzero simultaneously. Consequently
their complete generic-envelope criteria are equivalent, despite the changed
finite coefficient models. Local certificates construct an OLD represented
Picard region. Existence of enough initial certificates remains separate.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace
namespace FLT.Mazur.HilbertChart.AffineRestriction
open CartierAbel SchemePicard FCurve SchemeEffectiveEpiSections
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] relation fst snd
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R] {X : Scheme}
  (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  (d : ℕ) (V : Over (Spec (.of R))) [Etale V.hom] [IsAffine V.left]
  (c : (relativeFppfSheaf f).obj.obj (op V))
  {A : Over (Spec (.of R))} [IsAffine A.left] [IsIntegral A.left]
  (k : A ⟶ variableHilbertTest f d V) [IsOpenImmersion k.left]
variable (s : compatibleFunctions (fst f hL d V c k).left (snd f hL d V c k).left)
local notation "B" => invariantPrincipalSource f hL d V c k s
local notation "u" => invariantPrincipalSourceMap f hL d V c k s
local notation "l" => invariantPrincipalChart f hL d V c k s
variable [Nonempty (invariantPrincipalSource f hL d V c k s).left]
local instance principalGeneric_open : IsOpenImmersion (u).left :=
  inferInstanceAs (IsOpenImmersion (A.left.basicOpen s.val).ι)
local instance principalGeneric_integral : IsIntegral (B).left :=
  isIntegral_of_isOpenImmersion (u).left

/-- Nonzero admissibility is unchanged by a nonempty original invariant principal restriction. -/
theorem principal_denominators_ne_bot_iff :
    invariantEnvelopeDenominators f hL d V c l ≠ ⊥ ↔
      invariantEnvelopeDenominators f hL d V c k ≠ ⊥ := by
  constructor
  · intro hI
    obtain ⟨z, hz, hn⟩ := (Submodule.ne_bot_iff _).mp hI
    have hne : ((B).left.basicOpen z.val : Set (B).left).Nonempty := by
      apply (Opens.ne_bot_iff_nonempty _).mp
      intro he
      exact hn (Subtype.ext ((basicOpen_eq_bot_iff z.val).mp he))
    obtain ⟨a, ha, he⟩ := principalAdmissible_exists_original f hL d V c k s z hz
    apply (Submodule.ne_bot_iff _).mpr
    refine ⟨a, ha, ?_⟩
    intro hzero
    obtain ⟨x, hx⟩ := hne
    have hmem : (u).left x ∈ A.left.basicOpen a.val := by rw [he]; exact ⟨x, hx, rfl⟩
    rw [hzero] at hmem
    change (u).left x ∈ A.left.basicOpen 0 at hmem
    simp only [Scheme.basicOpen_zero, Opens.mem_bot] at hmem
  · intro hI
    obtain ⟨a, ha, hn⟩ := (Submodule.ne_bot_iff _).mp hI
    have hne : (A.left.basicOpen a.val : Set A.left).Nonempty := by
      apply (Opens.ne_bot_iff_nonempty _).mp
      intro he
      exact hn (Subtype.ext ((basicOpen_eq_bot_iff a.val).mp he))
    have hu : ((u).left.opensRange : Set A.left).Nonempty := by
      obtain ⟨x⟩ := ‹Nonempty (B).left›
      exact ⟨(u).left x, x, rfl⟩
    obtain ⟨y, hy, x, rfl⟩ := nonempty_preirreducible_inter
      (A.left.basicOpen a.val).isOpen (u).left.opensRange.isOpen hne hu
    have hx : x ∈ (B).left.basicOpen
        (principalInvariantRestriction f hL d V c k s a).val := by
      rw [principalInvariantRestriction_val, ← Scheme.preimage_basicOpen_top]
      exact hy
    apply (Submodule.ne_bot_iff _).mpr
    refine ⟨principalInvariantRestriction f hL d V c k s a,
      principalInvariantRestriction_admissible f hL d V c k s a ha, ?_⟩
    intro he
    rw [he] at hx
    change x ∈ (B).left.basicOpen 0 at hx
    simp only [Scheme.basicOpen_zero, Opens.mem_bot] at hx

/-- A recomputed generic-envelope certificate gives an actual represented OLD Picard region. -/
theorem oldPicardTarget_nonempty_of_principal_generic
    (hg : ∀ z : (prod B V).left,
      oldEnvelopeProjection f hL d V c l z =
          genericPoint (finiteKernelModel f hL d V c l).left →
        z ∈ (toEnvelope f hL d V c l).left.opensRange) :
    Nonempty (finiteModelPicardFppfTarget f hL d V c k).left := by
  apply finiteModelPicardFppfTarget_nonempty_of_denominators_ne_bot f hL d V c k
  apply (principal_denominators_ne_bot_iff f hL d V c k s).mp
  exact denominators_ne_bot_of_generic_envelope f hL d V c l hg

/-- The original generic obstruction persists through every nonempty invariant principal chart. -/
theorem principal_generic_envelope_iff :
    (∀ z : (prod B V).left,
      oldEnvelopeProjection f hL d V c l z =
          genericPoint (finiteKernelModel f hL d V c l).left →
        z ∈ (toEnvelope f hL d V c l).left.opensRange) ↔
    ∀ z : (prod A V).left,
      oldEnvelopeProjection f hL d V c k z =
          genericPoint (finiteKernelModel f hL d V c k).left →
        z ∈ (toEnvelope f hL d V c k).left.opensRange := by
  rw [← denominators_ne_bot_iff_generic_envelope,
    ← denominators_ne_bot_iff_generic_envelope]
  exact principal_denominators_ne_bot_iff f hL d V c k s

end FLT.Mazur.HilbertChart.AffineRestriction
