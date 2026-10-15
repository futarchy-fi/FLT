/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineHilbertEnvelopeFiberCount
public import FLT.Mazur.AffineHilbertFiniteFiberPrincipal

/-!
# Constructing original full-fiber neighborhoods from point counts

For finite translations, numerical certificates give invariant open
neighborhoods and affine principal refinements retaining the whole original
orbit. No closedness of the original relation endpoint is required. A
nonidentity original arrow suffices when the independent fiber has at most
two points; this includes disconnected two-point fibers.
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
local notation "p" => Over.Hom.left (fst f hL d V c k)
local notation "q" => Over.Hom.left (snd f hL d V c k)
local notation "π" => Over.Hom.left (prod.fst : prod A V ⟶ A)
local notation "e" => equivalence f hL d V c k

/-- Reflexivity and one distinct original arrow fill any independent fiber of size at most two. -/
theorem fullEnvelopeLocus_of_two_arrows (x : A.left)
    (z : (relation f hL d V c k).left) (hz : q z = x)
    (hne : z ≠ (e).r.left x) (hn : (π ⁻¹' {x}).ncard ≤ 2) :
    x ∈ fullEnvelopeLocus f hL d V c k := by
  apply (fullEnvelopeLocus_iff_fiber_ncard_le f hL d V c k x).mpr
  apply hn.trans
  have hr : q ((e).r.left x) = x :=
    congrArg (fun t : A ⟶ A ↦ t.left x) (e).reflexivity₂
  have hs : {z, (e).r.left x} ⊆ q ⁻¹' {x} := by
    intro y hy
    rcases Set.mem_insert_iff.mp hy with rfl | hy
    · exact hz
    · exact (Set.mem_singleton_iff.mp hy) ▸ hr
  have hc := Set.ncard_le_ncard hs (originalRelation_finite_fiber f hL d V c k x)
  simpa only [Set.ncard_pair hne] using hc

/-- Any strict branch deficit certifies that the chosen point has no full-envelope neighborhood. -/
theorem not_mem_fullInterior_of_fiber_ncard_lt (x : A.left)
    (h : (q ⁻¹' {x}).ncard < (π ⁻¹' {x}).ncard) :
    x ∉ fullEnvelopeInterior f hL d V c k := by
  intro hx
  exact h.not_ge ((fullEnvelopeLocus_iff_fiber_ncard_le f hL d V c k x).mp
    (interior_subset hx))

variable [IsFinite V.hom]

/-- Finite translation geometry upgrades the numerical certificate to an invariant OPEN domain. -/
theorem mem_fullInterior_iff_fiber_ncard_eq (x : A.left) :
    x ∈ fullEnvelopeInterior f hL d V c k ↔ (q ⁻¹' {x}).ncard = (π ⁻¹' {x}).ncard := by
  change x ∈ (fullEnvelopeInterior f hL d V c k : Set A.left) ↔ _
  rw [← fullEnvelopeLocus_iff_fiber_ncard_eq f hL d V c k x,
    fullEnvelopeLocus_eq_interior_of_finite]

variable [IsAffine A.left]

/-- A count certificate constructs a principal source retaining the entire original orbit. -/
theorem exists_countedFiber_orbit_principal (x : A.left)
    (hc : (π ⁻¹' {x}).ncard ≤ (q ⁻¹' {x}).ncard) :
    ∃ r : Γ(A.left, ⊤), x ∈ A.left.basicOpen r ∧
      A.left.basicOpen r ≤ fullEnvelopeInterior f hL d V c k ∧
      ∀ z : (relation f hL d V c k).left, q z = x → p z ∈ A.left.basicOpen r := by
  apply exists_fullInterior_orbit_principal f hL d V c k x
  change x ∈ (fullEnvelopeInterior f hL d V c k : Set A.left)
  rw [← fullEnvelopeLocus_eq_interior_of_finite]
  exact (fullEnvelopeLocus_iff_fiber_ncard_le f hL d V c k x).mpr hc

/-- The new affine chart has a full-fiber INTERIOR through the retained original point. -/
theorem exists_countedFiber_principal_interior (x : A.left)
    (hc : (π ⁻¹' {x}).ncard ≤ (q ⁻¹' {x}).ncard) :
    ∃ (r : Γ(A.left, ⊤)) (hr : x ∈ A.left.basicOpen r),
      A.left.basicOpen r ≤ fullEnvelopeInterior f hL d V c k ∧
      (⟨x, hr⟩ : (A.left.basicOpen r).toScheme) ∈
        fullEnvelopeInterior f hL d V c (orbitPrincipalChart f d V k r) :=
  exists_finite_fullFiber_principal_interior f hL d V c k x
    ((fullEnvelopeLocus_iff_fiber_ncard_le f hL d V c k x).mpr hc)

/-- Distinct original arrows produce a concrete affine refinement without closed endpoints. -/
theorem exists_twoArrow_principal_interior (x : A.left)
    (z : (relation f hL d V c k).left) (hz : q z = x)
    (hne : z ≠ (e).r.left x) (hn : (π ⁻¹' {x}).ncard ≤ 2) :
    ∃ (r : Γ(A.left, ⊤)) (hr : x ∈ A.left.basicOpen r),
      A.left.basicOpen r ≤ fullEnvelopeInterior f hL d V c k ∧
      (⟨x, hr⟩ : (A.left.basicOpen r).toScheme) ∈
        fullEnvelopeInterior f hL d V c (orbitPrincipalChart f d V k r) :=
  exists_finite_fullFiber_principal_interior f hL d V c k x
    (fullEnvelopeLocus_of_two_arrows f hL d V c k x z hz hne hn)

end FLT.Mazur.HilbertChart.AffineRestriction
