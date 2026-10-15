/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineHilbertFiniteFiberInvariants
public import FLT.Mazur.SchemeWholeFiberCoefficients

/-!
# Whole original envelopes over the unchanged finite coefficient target

The complement of the closed bad image defines an actual old target open.
Its principal neighborhoods pull back to ORIGINAL invariant admissible
coefficients. No norm on a freshly recomputed chart is transported.
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
  (d : ℕ) (V : Over (Spec (.of R))) [Etale V.hom]
  (c : (relativeFppfSheaf f).obj.obj (op V))
  {A : Over (Spec (.of R))} [IsAffine A.left]
  (k : A ⟶ variableHilbertTest f d V) [IsOpenImmersion k.left]
local notation "v" => Over.Hom.left (finiteKernelProjection f hL d V c k)
local notation "T" => (Over.left (finiteKernelModel f hL d V c k) : Scheme)
local notation "E" => (Over.left (prod A V) : Scheme)
local notation "π" => Over.Hom.left (prod.fst : prod A V ⟶ A)
local notation "j" => Over.Hom.left (toEnvelope f hL d V c k)
local notation "C" => compatibleFunctions
  (Over.Hom.left (fst f hL d V c k)) (Over.Hom.left (snd f hL d V c k))

/-- The complete independent translation envelope maps to the OLD finite model. -/
@[irreducible]
def oldEnvelopeProjection : E ⟶ T := π ≫ v

/-- The maximal old target open retaining whole original envelopes. -/
def oldEnvelopeTarget : (T).Opens :=
  SchemeWholeFiberOpen.locus (oldEnvelopeProjection f hL d V c k) (j).opensRange

/-- An old target section is literally an invariant original source section. -/
def oldTargetInvariantCoefficient (r : Γ(T, ⊤)) : C :=
  ⟨(v).appTop r, by
    have h := congrArg (fun a ↦ a.appTop r)
      (congrArg Over.Hom.left (finiteKernelProjection_condition f hL d V c k))
    exact h⟩

/-- The admissibility test uses the original complete envelope and the old coefficient map. -/
theorem oldTargetInvariantCoefficient_admissible_iff (r : Γ(T, ⊤)) :
    oldTargetInvariantCoefficient f hL d V c k r ∈
        invariantEnvelopeDenominators f hL d V c k ↔
      (T).basicOpen r ≤ oldEnvelopeTarget f hL d V c k := by
  rw [mem_invariantEnvelopeDenominators]
  change (π) ⁻¹ᵁ A.left.basicOpen ((v).appTop r) ≤ (j).opensRange ↔ _
  rw [← Scheme.preimage_basicOpen_top]
  unfold oldEnvelopeTarget oldEnvelopeProjection
  exact (SchemeWholeFiberOpen.le_locus_iff
    (π ≫ v) (j).opensRange ((T).basicOpen r)).symm

/-- Each original point over this old target open receives an actual admissible coefficient. -/
theorem oldEnvelopeTarget_source_coefficient (x : A.left)
    (hx : v x ∈ oldEnvelopeTarget f hL d V c k) :
    ∃ r : Γ(T, ⊤),
      oldTargetInvariantCoefficient f hL d V c k r ∈
        invariantEnvelopeDenominators f hL d V c k ∧
      x ∈ A.left.basicOpen (oldTargetInvariantCoefficient f hL d V c k r).val := by
  obtain ⟨r, hr, hE⟩ := SchemeWholeFiberOpen.exists_coefficient
    (oldEnvelopeProjection f hL d V c k) (j).opensRange (v x) hx
  refine ⟨r, ?_, ?_⟩
  · rw [oldTargetInvariantCoefficient_admissible_iff]
    apply SchemeWholeFiberOpen.le_locus
    rwa [Scheme.preimage_basicOpen_top]
  · change x ∈ A.left.basicOpen ((v).appTop r)
    rwa [← Scheme.preimage_basicOpen_top]

end FLT.Mazur.HilbertChart.AffineRestriction
