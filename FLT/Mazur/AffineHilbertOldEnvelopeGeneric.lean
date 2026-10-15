/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineHilbertOldEnvelopeTarget
public import FLT.Mazur.AffineHilbertAdmissibleIntegralSource

/-!
# Constructing old invariant denominators from complete generic envelopes

The original envelope has finite presentation over the old Noetherian model.
Chevalley therefore turns pointwise generic-envelope containment into actual
old invariant coefficients. Integral sources make the resulting coefficient
nonzero and yield a represented original Picard region.
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
  {A : Over (Spec (.of R))} [IsAffine A.left]
  (k : A ⟶ variableHilbertTest f d V) [IsOpenImmersion k.left]
local notation "v" => Over.Hom.left (finiteKernelProjection f hL d V c k)
local notation "T" => (Over.left (finiteKernelModel f hL d V c k) : Scheme)
local notation "E" => (Over.left (prod A V) : Scheme)
local notation "π" => Over.Hom.left (prod.fst : prod A V ⟶ A)
local notation "j" => Over.Hom.left (toEnvelope f hL d V c k)
local notation "e" => oldEnvelopeProjection f hL d V c k

/-- Affineness and finite presentation are derived for the complete original envelope. -/
instance oldEnvelopeProjection_locallyOfFinitePresentation : LocallyOfFinitePresentation e := by
  let _ : LocallyOfFiniteType π := by
    rw [← Over.prodLeftIsoPullback_hom_fst]
    infer_instance
  unfold oldEnvelopeProjection
  infer_instance

/-- The old envelope is affine, hence its complete old model projection is quasi-compact. -/
instance oldEnvelopeProjection_quasiCompact : QuasiCompact e := by
  let _ : IsAffine E := IsAffine.of_isIso (Over.prodLeftIsoPullback A V).hom
  infer_instance

include f hL d c k in
/-- No extra Noetherian hypothesis is imposed on the original envelope. -/
theorem oldEnvelope_isNoetherian : IsNoetherian E := by
  let _ := LocallyOfFiniteType.isLocallyNoetherian e
  let _ : IsAffine E := IsAffine.of_isIso (Over.prodLeftIsoPullback A V).hom
  exact ⟨⟩

/-- Generic pointwise fullness constructs an open in the OLD target, before any invariant input. -/
theorem oldEnvelopeTarget_generic_iff [IrreducibleSpace T] :
    genericPoint T ∈ oldEnvelopeTarget f hL d V c k ↔
      ∀ z : E, e z = genericPoint T → z ∈ (j).opensRange := by
  let _ := oldEnvelope_isNoetherian f hL d V c k
  exact SchemeWholeFiberOpen.genericPoint_mem_iff e (j).opensRange

variable [IsIntegral A.left]

/-- The constructed coefficient is nonzero in the ORIGINAL invariant ring. -/
theorem exists_nonzero_admissible_of_generic_envelope
    (hg : ∀ z : E, e z = genericPoint T → z ∈ (j).opensRange) :
    ∃ r : Γ(T, ⊤),
      oldTargetInvariantCoefficient f hL d V c k r ∈
        invariantEnvelopeDenominators f hL d V c k ∧
      oldTargetInvariantCoefficient f hL d V c k r ≠ 0 := by
  have hx : v (genericPoint A.left) ∈ oldEnvelopeTarget f hL d V c k := by
    rw [finiteKernelProjection_genericPoint]
    exact (oldEnvelopeTarget_generic_iff f hL d V c k).mpr hg
  obtain ⟨r, hr, hx⟩ := oldEnvelopeTarget_source_coefficient f hL d V c k
    (genericPoint A.left) hx
  refine ⟨r, hr, ?_⟩
  intro he
  rw [he] at hx
  change genericPoint A.left ∈ A.left.basicOpen 0 at hx
  simp only [Scheme.basicOpen_zero, Opens.mem_bot] at hx

/-- The original denominator ideal is now proved nonzero from generic envelope geometry. -/
theorem denominators_ne_bot_of_generic_envelope
    (hg : ∀ z : E, e z = genericPoint T → z ∈ (j).opensRange) :
    invariantEnvelopeDenominators f hL d V c k ≠ ⊥ := by
  obtain ⟨r, hr, hn⟩ := exists_nonzero_admissible_of_generic_envelope f hL d V c k hg
  exact (Submodule.ne_bot_iff _).mpr ⟨_, hr, hn⟩

/-- Pointwise generic envelope fullness produces a represented ORIGINAL Picard fppf region. -/
theorem picardFppfTarget_nonempty_of_generic_envelope
    (hg : ∀ z : E, e z = genericPoint T → z ∈ (j).opensRange) :
    Nonempty (finiteModelPicardFppfTarget f hL d V c k).left :=
  finiteModelPicardFppfTarget_nonempty_of_denominators_ne_bot f hL d V c k
    (denominators_ne_bot_of_generic_envelope f hL d V c k hg)

end FLT.Mazur.HilbertChart.AffineRestriction
