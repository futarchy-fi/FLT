/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineHilbertPicardFiberWitnesses
public import FLT.Mazur.FiniteFlatFiberCard

/-!
# Initial original full fibers from translation degree and Picard witnesses

Finite-flat degree of the original translation bounds every independent
fiber after base change. Enough distinct equal-class source points then
construct fullness. Degree at most one needs only the original identity
arrow and gives a full envelope on every source, without closed endpoints.
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
  (d : ℕ) (V : Over (Spec (.of R))) [Etale V.hom] [IsAffine V.left] [IsFinite V.hom]
  (c : (relativeFppfSheaf f).obj.obj (op V))
  {A : Over (Spec (.of R))} (k : A ⟶ variableHilbertTest f d V)
  [IsOpenImmersion k.left]
local notation "q" => Over.Hom.left (snd f hL d V c k)
local notation "π" => Over.Hom.left (prod.fst : prod A V ⟶ A)
local notation "σ" => sectionAt f hL d V c k
local notation "e" => equivalence f hL d V c k

omit [Algebra.FiniteType ℤ R] [IsAffine V.left] in
/-- The original translation degree bounds all independent residue-field branches. -/
theorem independentEnvelope_fiber_ncard_le_degree (x : A.left) :
    (π ⁻¹' {x}).ncard ≤ V.hom.finrank (A.hom x) := by
  have h : IsPullback (prod.snd : prod A V ⟶ V).left π V.hom A.hom :=
    (Over.isPullback_of_binaryFan_isLimit _ (prodIsProd A V)).flip
  let _ : IsFinite π := MorphismProperty.of_isPullback h
    (inferInstanceAs (IsFinite V.hom))
  let _ : Flat π := MorphismProperty.of_isPullback h (inferInstanceAs (Flat V.hom))
  have hc := FiniteFlatFiberCard.fiber_ncard_le_finrank π x
  rwa [Scheme.Hom.finrank_of_isPullback _ _ _ _ h] at hc

/-- A degree bound and distinct equal-class points construct full original fibers. -/
theorem fullEnvelopeLocus_of_degree_picard_witnesses {T : Over (Spec (.of R))}
    (b : T ⟶ A) {n : ℕ} (a : Fin n → (T ⟶ A)) (t : T.left)
    (ha : Function.Injective (fun i ↦ (a i).left t))
    (hc : ∀ i, (relativeFppfSheaf f).obj.map (a i).op σ =
      (relativeFppfSheaf f).obj.map b.op σ)
    (hn : V.hom.finrank (A.hom (b.left t)) ≤ n) :
    b.left t ∈ fullEnvelopeLocus f hL d V c k :=
  fullEnvelopeLocus_of_picard_witnesses f hL d V c k b a t ha hc
    ((independentEnvelope_fiber_ncard_le_degree V (b.left t)).trans hn)

/-- Degree at most one needs only reflexivity, even without a closed original endpoint. -/
theorem fullEnvelopeLocus_of_degree_le_one (x : A.left)
    (hn : V.hom.finrank (A.hom x) ≤ 1) : x ∈ fullEnvelopeLocus f hL d V c k := by
  apply (fullEnvelopeLocus_iff_fiber_ncard_le f hL d V c k x).mpr
  apply ((independentEnvelope_fiber_ncard_le_degree V x).trans hn).trans
  apply Nat.succ_le_of_lt
  apply (Set.ncard_pos (originalRelation_finite_fiber f hL d V c k x)).mpr
  exact ⟨(e).r.left x, congrArg (fun t : A ⟶ A ↦ t.left x) (e).reflexivity₂⟩

/-- Degree at most one on the source image constructs the whole original envelope isomorphism. -/
theorem toEnvelope_isIso_of_degree_le_one
    (hn : ∀ x : A.left, V.hom.finrank (A.hom x) ≤ 1) :
    IsIso (toEnvelope f hL d V c k).left := by
  apply (isIso_iff_isOpenImmersion_and_surjective _).mpr
  refine ⟨inferInstance, ⟨?_⟩⟩
  intro z
  exact (mem_fullFiberLocus π (toEnvelope f hL d V c k).left.opensRange (π z)).mp
    (fullEnvelopeLocus_of_degree_le_one f hL d V c k (π z) (hn (π z))) z rfl

/-- Degree two and a distinct equal-class pair construct a principal full-interior chart. -/
theorem exists_degreeTwo_picard_principal [IsAffine A.left] {T : Over (Spec (.of R))}
    (a b : T ⟶ A) (t : T.left)
    (hc : (relativeFppfSheaf f).obj.map a.op σ = (relativeFppfSheaf f).obj.map b.op σ)
    (hne : a.left t ≠ b.left t) (hn : V.hom.finrank (A.hom (b.left t)) ≤ 2) :
    ∃ (r : Γ(A.left, ⊤)) (hr : b.left t ∈ A.left.basicOpen r),
      A.left.basicOpen r ≤ fullEnvelopeInterior f hL d V c k ∧
      (⟨b.left t, hr⟩ : (A.left.basicOpen r).toScheme) ∈
        fullEnvelopeInterior f hL d V c (orbitPrincipalChart f d V k r) :=
  exists_picardPair_principal_interior f hL d V c k a b t hc hne
    ((independentEnvelope_fiber_ncard_le_degree V (b.left t)).trans hn)

end FLT.Mazur.HilbertChart.AffineRestriction
