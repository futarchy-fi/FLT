/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineHilbertOldEnvelopeGeneric

/-!
# Exact generic geometric criterion for original nonzero admissibility

On an integral original source, any nonzero admissible coefficient retains
the whole envelope over the generic OLD target point. Conversely those
pointwise envelope data construct a nonzero original invariant coefficient.
This makes the missing geometric existence condition explicit, not an input
coefficient or an assumed relation representative.
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
local notation "v" => Over.Hom.left (finiteKernelProjection f hL d V c k)
local notation "T" => (Over.left (finiteKernelModel f hL d V c k) : Scheme)
local notation "E" => (Over.left (prod A V) : Scheme)
local notation "π" => Over.Hom.left (prod.fst : prod A V ⟶ A)
local notation "j" => Over.Hom.left (toEnvelope f hL d V c k)
local notation "e" => oldEnvelopeProjection f hL d V c k
local notation "C" => compatibleFunctions
  (Over.Hom.left (fst f hL d V c k)) (Over.Hom.left (snd f hL d V c k))

omit [IsAffine V.left] in
/-- One nonzero original coefficient retains every independent generic-envelope branch. -/
theorem generic_envelope_of_nonzero_admissible (s : C)
    (hs : s ∈ invariantEnvelopeDenominators f hL d V c k) (hn : s ≠ 0) :
    ∀ z : E, e z = genericPoint T → z ∈ (j).opensRange := by
  have hne : (A.left.basicOpen s.val : Set A.left).Nonempty := by
    apply (Opens.ne_bot_iff_nonempty _).mp
    intro he
    exact hn (Subtype.ext ((basicOpen_eq_bot_iff s.val).mp he))
  intro z hz
  have hp : v (π z) = genericPoint T := by
    simpa only [oldEnvelopeProjection, Scheme.Hom.comp_apply] using hz
  obtain ⟨t, ht, hx⟩ := integral_generic_admissible_coverage f hL d V c k s hs hne
    (π z) hp
  exact (mem_invariantEnvelopeDenominators f hL d V c k t).mp ht hx

/-- Nonzero original admissibility is exactly full independent-envelope generic containment. -/
theorem denominators_ne_bot_iff_generic_envelope :
    invariantEnvelopeDenominators f hL d V c k ≠ ⊥ ↔
      ∀ z : E, e z = genericPoint T → z ∈ (j).opensRange := by
  refine ⟨?_, denominators_ne_bot_of_generic_envelope f hL d V c k⟩
  intro hI
  obtain ⟨s, hs, hn⟩ := (Submodule.ne_bot_iff _).mp hI
  exact generic_envelope_of_nonzero_admissible f hL d V c k s hs hn

/-- The original denominator ideal is nonzero exactly when the constructed OLD open is nonempty. -/
theorem denominators_ne_bot_iff_oldEnvelopeTarget_nonempty :
    invariantEnvelopeDenominators f hL d V c k ≠ ⊥ ↔
      (oldEnvelopeTarget f hL d V c k : Set T).Nonempty := by
  rw [denominators_ne_bot_iff_generic_envelope]
  let _ := oldEnvelope_isNoetherian f hL d V c k
  exact (SchemeWholeFiberOpen.nonempty_iff_genericFiber e (j).opensRange).symm

end FLT.Mazur.HilbertChart.AffineRestriction
