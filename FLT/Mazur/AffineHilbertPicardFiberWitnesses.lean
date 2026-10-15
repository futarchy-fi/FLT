/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineHilbertCountedFiberNeighborhood

/-!
# Constructing full original fibers from actual Picard class equalities

Maps on a common scheme test with equal original Picard classes construct
original relation arrows. Distinct source points give distinct arrows.
Enough such points fill the independent finite fiber, without preselected
relation representatives, connectedness, or closed relation endpoints.
The test may be nonaffine or nonreduced.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart.AffineRestriction
open CartierAbel SchemePicard FCurve
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] relation fst snd
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R] {X : Scheme}
  (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  (d : ℕ) (V : Over (Spec (.of R))) [Etale V.hom] [IsAffine V.left]
  (c : (relativeFppfSheaf f).obj.obj (op V))
  {A : Over (Spec (.of R))} (k : A ⟶ variableHilbertTest f d V)
  [IsOpenImmersion k.left]
local notation "p" => fst f hL d V c k
local notation "q" => snd f hL d V c k
local notation "π" => Over.Hom.left (prod.fst : prod A V ⟶ A)
local notation "σ" => sectionAt f hL d V c k
local notation "e" => equivalence f hL d V c k

/-- Actual Picard equalities on one test construct all arrows needed for the numerical bound. -/
theorem fullEnvelopeLocus_of_picard_witnesses {T : Over (Spec (.of R))}
    (b : T ⟶ A) {n : ℕ} (a : Fin n → (T ⟶ A)) (t : T.left)
    (ha : Function.Injective (fun i ↦ (a i).left t))
    (hc : ∀ i, (relativeFppfSheaf f).obj.map (a i).op σ =
      (relativeFppfSheaf f).obj.map b.op σ)
    (hn : (π ⁻¹' {b.left t}).ncard ≤ n) :
    b.left t ∈ fullEnvelopeLocus f hL d V c k := by
  have hl (i : Fin n) := lift f hL d V c k (a i) b (hc i)
  let z (i : Fin n) : T ⟶ relation f hL d V c k := (hl i).choose
  have hp (i : Fin n) : z i ≫ p = a i := (hl i).choose_spec.1.1
  have hq (i : Fin n) : z i ≫ q = b := (hl i).choose_spec.1.2
  have hpt (i : Fin n) : (p).left ((z i).left t) = (a i).left t :=
    congrArg (fun u : T ⟶ A ↦ u.left t) (hp i)
  have hqt (i : Fin n) : (q).left ((z i).left t) = b.left t :=
    congrArg (fun u : T ⟶ A ↦ u.left t) (hq i)
  apply fullEnvelopeLocus_of_fiber_witnesses f hL d V c k (b.left t)
    (fun i ↦ (z i).left t) _ hqt hn
  intro i j hij
  apply ha
  exact (hpt i).symm.trans ((congrArg (p).left hij).trans (hpt j))

/-- Two distinct original source points with the same Picard class fill a two-branch fiber. -/
theorem fullEnvelopeLocus_of_picard_pair {T : Over (Spec (.of R))}
    (a b : T ⟶ A) (t : T.left)
    (hc : (relativeFppfSheaf f).obj.map a.op σ = (relativeFppfSheaf f).obj.map b.op σ)
    (hne : a.left t ≠ b.left t) (hn : (π ⁻¹' {b.left t}).ncard ≤ 2) :
    b.left t ∈ fullEnvelopeLocus f hL d V c k := by
  obtain ⟨z, hz, _⟩ := lift f hL d V c k a b hc
  have hp : (p).left (z.left t) = a.left t :=
    congrArg (fun u : T ⟶ A ↦ u.left t) hz.1
  have hq : (q).left (z.left t) = b.left t :=
    congrArg (fun u : T ⟶ A ↦ u.left t) hz.2
  apply fullEnvelopeLocus_of_two_arrows f hL d V c k (b.left t) (z.left t) hq _ hn
  intro he
  apply hne
  rw [← hp, he]
  exact congrArg (fun u : A ⟶ A ↦ u.left (b.left t)) (e).reflexivity₁

variable [IsFinite V.hom] [IsAffine A.left]

/-- Equal original Picard classes construct a principal chart with a nonempty full interior. -/
theorem exists_picardPair_principal_interior {T : Over (Spec (.of R))}
    (a b : T ⟶ A) (t : T.left)
    (hc : (relativeFppfSheaf f).obj.map a.op σ = (relativeFppfSheaf f).obj.map b.op σ)
    (hne : a.left t ≠ b.left t) (hn : (π ⁻¹' {b.left t}).ncard ≤ 2) :
    ∃ (r : Γ(A.left, ⊤)) (hr : b.left t ∈ A.left.basicOpen r),
      A.left.basicOpen r ≤ fullEnvelopeInterior f hL d V c k ∧
      (⟨b.left t, hr⟩ : (A.left.basicOpen r).toScheme) ∈
        fullEnvelopeInterior f hL d V c (orbitPrincipalChart f d V k r) :=
  exists_finite_fullFiber_principal_interior f hL d V c k (b.left t)
    (fullEnvelopeLocus_of_picard_pair f hL d V c k a b t hc hne hn)

end FLT.Mazur.HilbertChart.AffineRestriction
