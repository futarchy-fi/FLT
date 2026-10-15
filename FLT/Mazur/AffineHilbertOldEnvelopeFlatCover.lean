/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineHilbertOldEnvelopeEffective
public import FLT.Mazur.AffineHilbertAdmissibleFlatImage

/-!
# Exact admissible coverage of the old whole-envelope fppf region

The original admissible flat images cover precisely the intersection of the
old whole-envelope target with its complete-source fppf locus. This gives an
actual fppf target and exact coverage there, without integral or global-flat
hypotheses. Coverage of arbitrary original classes is still separate.
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
local notation "W" => oldEnvelopeTarget f hL d V c k

/-- The actual old target retaining whole original envelopes and complete fppf sources. -/
def oldEnvelopeFppfOpen : (T).Opens := W ⊓ SchemeFppfTargetOpen.locus v

/-- Every admissible flat image lies in the old whole-envelope target. -/
theorem admissibleFlatImage_le_oldEnvelopeTarget (s : C)
    (hs : s ∈ invariantEnvelopeDenominators f hL d V c k) :
    admissibleFlatImage f hL d V c k s ≤ W := by
  apply SchemeWholeFiberOpen.le_locus
  intro z hz
  change oldEnvelopeProjection f hL d V c k z ∈
    admissibleFlatImage f hL d V c k s at hz
  have hx : v (π z) ∈ admissibleFlatImage f hL d V c k s := by
    simpa only [oldEnvelopeProjection, Scheme.Hom.comp_apply] using hz
  exact (mem_invariantEnvelopeDenominators f hL d V c k s).mp hs
    (admissibleFlatImage_source_le f hL d V c k s hx)

/-- This open has exactly the coverage furnished by actual original admissible coefficients. -/
theorem mem_oldEnvelopeFppfOpen_iff (y : T) :
    y ∈ oldEnvelopeFppfOpen f hL d V c k ↔
      ∃ s : C, s ∈ invariantEnvelopeDenominators f hL d V c k ∧
        y ∈ admissibleFlatImage f hL d V c k s := by
  constructor
  · rintro ⟨hy, hf⟩
    have hh : y ∈ (SchemeFppfTargetOpen.locus v : Set T) := hf
    rw [SchemeFppfTargetOpen.coe_locus] at hh
    obtain ⟨⟨x, rfl⟩, hflat⟩ := hh
    obtain ⟨r, hr, hx⟩ := oldEnvelopeTarget_source_coefficient f hL d V c k x hy
    exact ⟨oldTargetInvariantCoefficient f hL d V c k r, hr,
      admissibleFlatImage_contains f hL d V c k _ x hx hflat⟩
  · rintro ⟨s, hs, hy⟩
    exact ⟨admissibleFlatImage_le_oldEnvelopeTarget f hL d V c k s hs hy,
      SchemeFlatSourceImage.image_le_fppf v (A.left.basicOpen s.val) hy⟩

/-- The complete original source over the exact covered target is flat. -/
theorem oldEnvelopeFppfOpen_flat :
    Flat (pullback.snd v (oldEnvelopeFppfOpen f hL d V c k).ι) :=
  ((SchemeFppfTargetOpen.le_locus_iff v _).mp inf_le_right).1

/-- Every point of the covered old target has an actual original source point. -/
theorem oldEnvelopeFppfOpen_surjective :
    Surjective (pullback.snd v (oldEnvelopeFppfOpen f hL d V c k).ι) :=
  ((SchemeFppfTargetOpen.le_locus_iff v _).mp inf_le_right).2

end FLT.Mazur.HilbertChart.AffineRestriction
