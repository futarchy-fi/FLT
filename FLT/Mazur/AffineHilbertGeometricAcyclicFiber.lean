/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineHilbertAcyclicBranchLift
public import FLT.Mazur.AffineHilbertGeometricFiberSections
public import FLT.Mazur.AffineHilbertFiniteFiberPrincipal

/-!
# Full original fibers from constructed geometric Hilbert lifts

Finite étale fiber enumeration and acyclic translated divisor classes build
the original relation witnesses, rather than taking them as hypotheses.
Their envelope coordinates prove distinctness, including nonsplit branches.
The remaining geometric inputs are acyclicity with the fixed degree and
retention of the constructed parameters in the original source open.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart.AffineRestriction
open CartierAbel SchemePicard FCurve
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] relation fst snd
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R] {X : Scheme}
  (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  (d : ℕ) (V : Over (Spec (.of R))) [Etale V.hom] [IsAffine V.left]
  (c : (relativeFppfSheaf f).obj.obj (op V))
  {A : Over (Spec (.of R))} (k : A ⟶ variableHilbertTest f d V)
  [IsOpenImmersion k.left]
  {K : Type} [Field K] {t : Spec (.of K) ⟶ Spec (.of R)} (b : Over.mk t ⟶ A)
local notation "η" => (default : Spec (CommRingCat.of K))
local notation "σ" => sectionAt f hL d V c k
local notation "s" => CategoryTheory.Functor.map
  (ObjectProperty.FullSubcategory.obj (relativeFppfSheaf f)) (Quiver.Hom.op b) σ
local notation "π" => Over.Hom.left (prod.fst : prod A V ⟶ A)

/-- Actual acyclic Hilbert lifts of enough independent coordinates fill the original fiber. -/
theorem fullEnvelopeLocus_of_acyclic_geometric_sections {n : ℕ}
    (e : Fin n → (Over.mk t ⟶ prod A V)) (he : ∀ i, e i ≫ prod.fst = b)
    (hi : Function.Injective (fun i ↦ (e i).left η))
    (hn : (π ⁻¹' {b.left η}).ncard ≤ n)
    (hA : ∀ i, s * (relativeFppfSheaf f).obj.map (e i ≫ prod.snd).op c ∈
      (acyclicDegreePicardSubfunctor f d).obj (op (Over.mk t)))
    (hr : ∀ i, (acyclicTranslationLift f hL d V c s (e i ≫ prod.snd) (hA i)).left
      η ∈ Set.range k.left) :
    b.left η ∈ fullEnvelopeLocus f hL d V c k := by
  have hl (i : Fin n) := exists_acyclic_geometric_relation_lift f hL d V c k b
    (e i ≫ prod.snd) rfl (hA i) η (hr i)
  choose z hz using hl
  have hz' (i : Fin n) : z i ≫ toEnvelope f hL d V c k = e i := by
    rw [hz i]
    apply prod.hom_ext
    · rw [prod.lift_fst, he i]
    · rw [prod.lift_snd]
  apply fullEnvelopeLocus_of_fiber_witnesses f hL d V c k (b.left η)
    (fun i ↦ (z i).left η)
    (geometric_relation_lifts_injective V (toEnvelope f hL d V c k) e hi z hz') _ hn
  intro i
  have hq : z i ≫ snd f hL d V c k = b := by
    rw [← toEnvelope_test, ← Category.assoc, hz', he]
  exact congrArg (fun a : Over.mk t ⟶ A ↦ a.left η) hq

/-- Splitting constructs the finite witness family on the chosen separably closed test. -/
theorem fullEnvelopeLocus_of_all_geometric_translations [IsSepClosed K]
    (hA : ∀ v : Over.mk t ⟶ V, s * (relativeFppfSheaf f).obj.map v.op c ∈
      (acyclicDegreePicardSubfunctor f d).obj (op (Over.mk t)))
    (hr : ∀ v : Over.mk t ⟶ V,
      (acyclicTranslationLift f hL d V c s v (hA v)).left η ∈ Set.range k.left) :
    b.left η ∈ fullEnvelopeLocus f hL d V c k := by
  obtain ⟨e, he, hi, _⟩ := exists_independent_geometric_sections V b
  exact fullEnvelopeLocus_of_acyclic_geometric_sections f hL d V c k b e he hi le_rfl
    (fun i ↦ hA (e i ≫ prod.snd)) (fun i ↦ hr (e i ≫ prod.snd))

/-- The constructed geometric witnesses give a principal chart retaining its new full interior. -/
theorem exists_geometric_acyclic_principal [IsSepClosed K] [IsFinite V.hom] [IsAffine A.left]
    (hA : ∀ v : Over.mk t ⟶ V, s * (relativeFppfSheaf f).obj.map v.op c ∈
      (acyclicDegreePicardSubfunctor f d).obj (op (Over.mk t)))
    (hr : ∀ v : Over.mk t ⟶ V,
      (acyclicTranslationLift f hL d V c s v (hA v)).left η ∈ Set.range k.left) :
    ∃ (r : Γ(A.left, ⊤)) (hr : b.left η ∈ A.left.basicOpen r),
      A.left.basicOpen r ≤ fullEnvelopeInterior f hL d V c k ∧
      (⟨b.left η, hr⟩ : (A.left.basicOpen r).toScheme) ∈
        fullEnvelopeInterior f hL d V c (orbitPrincipalChart f d V k r) :=
  exists_finite_fullFiber_principal_interior f hL d V c k (b.left η)
    (fullEnvelopeLocus_of_all_geometric_translations f hL d V c k b hA hr)

end FLT.Mazur.HilbertChart.AffineRestriction
