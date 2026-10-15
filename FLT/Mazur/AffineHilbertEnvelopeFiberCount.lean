/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineHilbertConnectedEnvelopeFiber
public import FLT.Mazur.FiniteFiberImageCard
public import FLT.Mazur.VariableHilbertFiniteRelationFibers

/-!
# Original envelope fullness from finite point counts

The original relation embeds in the independent translation envelope. Its
actual fibers are finite, and their missing-branch count is exactly the
deficit between the two point counts. Equality fills disconnected fibers
without closed endpoints or connectedness. These are topological point
counts, not algebraic degrees over potentially nonsplit residue fields.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart.AffineRestriction
open CartierAbel SchemePicard FCurve SchemeOpenEnvelope
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] relation fst snd
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R] {X : Scheme}
  (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  (d : ℕ) (V : Over (Spec (.of R))) [Etale V.hom] [IsAffine V.left]
  (c : (relativeFppfSheaf f).obj.obj (op V))
  {A : Over (Spec (.of R))} (k : A ⟶ variableHilbertTest f d V)
  [IsOpenImmersion k.left]
local notation "q" => Over.Hom.left (snd f hL d V c k)
local notation "j" => Over.Hom.left (toEnvelope f hL d V c k)
local notation "π" => Over.Hom.left (prod.fst : prod A V ⟶ A)

omit [Algebra.FiniteType ℤ R] in
/-- The independent envelope has finite fibers even if the original source is not affine. -/
theorem independentEnvelope_finite_fiber (x : A.left) : (π ⁻¹' {x}).Finite := by
  have hp : π = (Over.prodLeftIsoPullback A V).hom ≫ pullback.fst A.hom V.hom :=
    (Over.prodLeftIsoPullback_hom_fst A V).symm
  let _ : Etale π := by rw [hp]; infer_instance
  let _ : QuasiCompact π := by rw [hp]; infer_instance
  let _ : LocallyQuasiFinite π := by
    constructor
    intro U hU W hW h
    have hφ := (π).etale_appLE hU hW h
    algebraize [((π).appLE U W h).hom]
    exact inferInstanceAs (Algebra.QuasiFinite _ _)
  exact (π).finite_preimage_singleton x

omit [Etale V.hom] [IsAffine V.left] [IsOpenImmersion k.left] in
/-- The original envelope inclusion preserves its actual second-endpoint fiber. -/
theorem toEnvelope_fiber_eq (z : (relation f hL d V c k).left) : π (j z) = q z :=
  congrArg (fun t : relation f hL d V c k ⟶ A ↦ t.left z)
    (toEnvelope_test f hL d V c k)

/-- Finiteness of the ORIGINAL endpoint fiber follows by its envelope injection. -/
theorem originalRelation_finite_fiber (x : A.left) : (q ⁻¹' {x}).Finite :=
  FiniteFiberImageCard.finite_fiber j π q (toEnvelope_fiber_eq f hL d V c k)
    (j).injective x (independentEnvelope_finite_fiber V x)

/-- The original relation's point count is bounded by the full independent fiber count. -/
theorem originalRelation_fiber_ncard_le (x : A.left) :
    (q ⁻¹' {x}).ncard ≤ (π ⁻¹' {x}).ncard :=
  FiniteFiberImageCard.fiber_ncard_le j π q (toEnvelope_fiber_eq f hL d V c k)
    (j).injective x (independentEnvelope_finite_fiber V x)

/-- The exact deficit counts all missing scheme points, including nonsplit residue branches. -/
theorem originalEnvelope_missing_ncard_add (x : A.left) :
    ((π ⁻¹' {x}) \ Set.range j).ncard + (q ⁻¹' {x}).ncard = (π ⁻¹' {x}).ncard :=
  FiniteFiberImageCard.missing_ncard_add j π q (toEnvelope_fiber_eq f hL d V c k)
    (j).injective x (independentEnvelope_finite_fiber V x)

/-- A reverse numerical bound is an exact certificate for full original fibers. -/
theorem fullEnvelopeLocus_iff_fiber_ncard_le (x : A.left) :
    x ∈ fullEnvelopeLocus f hL d V c k ↔ (π ⁻¹' {x}).ncard ≤ (q ⁻¹' {x}).ncard := by
  rw [fullEnvelopeLocus, mem_fullFiberLocus]
  exact FiniteFiberImageCard.fiber_subset_range_iff j π q
    (toEnvelope_fiber_eq f hL d V c k) (j).injective x
    (independentEnvelope_finite_fiber V x)

/-- Equal actual fiber counts detect fullness without any connectedness assumption. -/
theorem fullEnvelopeLocus_iff_fiber_ncard_eq (x : A.left) :
    x ∈ fullEnvelopeLocus f hL d V c k ↔ (q ⁻¹' {x}).ncard = (π ⁻¹' {x}).ncard := by
  rw [fullEnvelopeLocus, mem_fullFiberLocus]
  exact FiniteFiberImageCard.fiber_subset_range_iff_eq j π q
    (toEnvelope_fiber_eq f hL d V c k) (j).injective x
    (independentEnvelope_finite_fiber V x)

/-- Distinct original relation points construct fullness from an independent upper bound. -/
theorem fullEnvelopeLocus_of_fiber_witnesses (x : A.left) {n : ℕ}
    (s : Fin n → (relation f hL d V c k).left) (hs : Function.Injective s)
    (hq : ∀ i, q (s i) = x) (hn : (π ⁻¹' {x}).ncard ≤ n) :
    x ∈ fullEnvelopeLocus f hL d V c k := by
  apply (mem_fullFiberLocus π (j).opensRange x).mpr
  exact FiniteFiberImageCard.fiber_subset_range_of_witnesses j π q
    (toEnvelope_fiber_eq f hL d V c k) (j).injective x
    (independentEnvelope_finite_fiber V x) s hs hq hn

end FLT.Mazur.HilbertChart.AffineRestriction
