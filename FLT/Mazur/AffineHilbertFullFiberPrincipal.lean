/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineHilbertFullFiberRestriction

/-!
# Affine principal restrictions retaining a chosen full fiber

Inside the maximal open full-envelope domain, prime avoidance constructs a
principal affine source containing the entire finite original orbit. Its
actual restricted chart retains the chosen full independent fiber. The
coefficient is not asserted invariant, nor is the new point asserted to lie
in the interior of the restricted full-fiber locus.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart.AffineRestriction
open CartierAbel SchemePicard FCurve SchemeOpenEnvelope
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R] {X : Scheme}
  (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  (d : ℕ) (V : Over (Spec (.of R)))
  (c : (relativeFppfSheaf f).obj.obj (op V))
  {A : Over (Spec (.of R))} (k : A ⟶ variableHilbertTest f d V)
  [IsOpenImmersion k.left]
local notation "p" => fst f hL d V c k
local notation "q" => snd f hL d V c k

/-- The actual principal source with its original structural map. -/
def orbitPrincipalSource (r : Γ(A.left, ⊤)) : Over (Spec (.of R)) :=
  Over.mk ((A.left.basicOpen r).ι ≫ A.hom)

/-- The principal source inclusion retains the original source coordinates. -/
def orbitPrincipalSourceMap (r : Γ(A.left, ⊤)) : orbitPrincipalSource r ⟶ A :=
  Over.homMk (A.left.basicOpen r).ι

/-- The actual open chart on a principal source, without an invariance premise. -/
@[irreducible]
def orbitPrincipalChart (r : Γ(A.left, ⊤)) :
    orbitPrincipalSource r ⟶ variableHilbertTest f d V := orbitPrincipalSourceMap r ≫ k

instance orbitPrincipalSource_affine [IsAffine A.left] (r : Γ(A.left, ⊤)) :
    IsAffine (orbitPrincipalSource r).left :=
  inferInstanceAs (IsAffine (A.left.basicOpen r).toScheme)

instance orbitPrincipalChart_isOpenImmersion (r : Γ(A.left, ⊤)) :
    IsOpenImmersion (orbitPrincipalChart f d V k r).left := by
  unfold orbitPrincipalChart orbitPrincipalSourceMap
  change IsOpenImmersion ((A.left.basicOpen r).ι ≫ k.left)
  infer_instance

variable [IsAffine A.left] [IsAffine V.left] [Etale V.hom]

/-- Prime avoidance constructs one coefficient retaining every original endpoint over the point. -/
theorem exists_fullInterior_orbit_principal (x : A.left)
    (hx : x ∈ fullEnvelopeInterior f hL d V c k) :
    ∃ r : Γ(A.left, ⊤), x ∈ A.left.basicOpen r ∧
      A.left.basicOpen r ≤ fullEnvelopeInterior f hL d V c k ∧
      ∀ z : (relation f hL d V c k).left,
        (q).left z = x → (p).left z ∈ A.left.basicOpen r := by
  let s : Set A.left := (p).left '' ((q).left ⁻¹' {x}) ∪ {x}
  have hs : s.Finite := ((snd_finite_fiber f hL d V c k x).image (p).left).union
    (Set.finite_singleton x)
  have hU : s ⊆ fullEnvelopeInterior f hL d V c k := by
    rintro y (⟨z, hz, rfl⟩ | hy)
    · have he := Set.ext_iff.mp
        (congrArg SetLike.coe (fullEnvelopeInterior_invariant f hL d V c k)) z
      change (p).left z ∈ fullEnvelopeInterior f hL d V c k ↔
        (q).left z ∈ fullEnvelopeInterior f hL d V c k at he
      apply he.mpr
      change (q).left z = x at hz
      rwa [hz]
    · exact (Set.mem_singleton_iff.mp hy).symm ▸ hx
  obtain ⟨r, hr, hsub⟩ := AffineEnvelopeFiniteNeighborhood.exists_envelope_principal
    (fullEnvelopeInterior f hL d V c k) s hs hU
  exact ⟨r, hr (Or.inr rfl), hsub, fun z hz ↦ hr (Or.inl ⟨z, hz, rfl⟩)⟩

/-- The constructed affine principal source retains the actual full independent fiber. -/
theorem exists_fullInterior_principal_chart (x : A.left)
    (hx : x ∈ fullEnvelopeInterior f hL d V c k) :
    ∃ (r : Γ(A.left, ⊤)) (hr : x ∈ A.left.basicOpen r),
      A.left.basicOpen r ≤ fullEnvelopeInterior f hL d V c k ∧
      (⟨x, hr⟩ : (A.left.basicOpen r).toScheme) ∈
        fullEnvelopeLocus f hL d V c (orbitPrincipalChart f d V k r) := by
  obtain ⟨r, hr, hsub, horbit⟩ := exists_fullInterior_orbit_principal f hL d V c k x hx
  refine ⟨r, hr, hsub, ?_⟩
  unfold orbitPrincipalChart
  let v := orbitPrincipalSourceMap (A := A) r
  let _ : IsOpenImmersion v.left := inferInstanceAs (IsOpenImmersion (A.left.basicOpen r).ι)
  apply nested_fullFiber_retained f hL d V c k v ⟨x, hr⟩
  · exact interior_subset hx
  · intro z hz
    exact ⟨⟨(p).left z, horbit z hz⟩, rfl⟩

end FLT.Mazur.HilbertChart.AffineRestriction
