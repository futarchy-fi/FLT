/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RelativeRelationBasePrincipal
public import FLT.Mazur.SchemeOpenEnvelopeInteriorTests

/-!
# Constructing original invariant denominators from whole base fibers

For an orbit domain W and an open O, remove the closure of the base image
of the source points of W outside O. At every retained base point, affine
principal neighborhoods give original invariant scalars on W supported in O.
The construction needs neither an affine quotient nor an invariant principal basis.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace
universe u
namespace FLT.Mazur.RelativeRelationOrbit
open SchemeOpenEnvelope
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {S : Scheme.{u}} {D A : Over S} {p q : D ⟶ A}
  (e : CategoryTheory.EquivalenceRelation p q) (W O : Opens (Orbit e))
set_option quotPrecheck false
local notation "E" => (pullOpen e W).val
local notation "b" => invariantLocallyRingedBaseMap e

/-- The largest base open whose entire source over W maps into O. -/
def baseFiberOpen : S.Opens :=
  fullFiberInterior ((E).ι ≫ A.hom) ((E).ι ⁻¹ᵁ (pullOpen e O).val)

/-- Its defining test retains the closure of the actual bad base image. -/
theorem mem_baseFiberOpen (x : S) :
    x ∈ baseFiberOpen e W O ↔
      x ∉ closure (((E).ι ≫ A.hom) ''
        ((E).ι ⁻¹ᵁ (pullOpen e O).val : Set (E).toScheme)ᶜ) :=
  mem_fullFiberInterior _ _ x

/-- Whole-fiber containment is exactly containment of the original quotient base preimage. -/
theorem baseOpen_le_baseFiberOpen_iff (B : S.Opens) :
    B ≤ baseFiberOpen e W O ↔ W ⊓ (Opens.map (b).base).obj B ≤ O := by
  rw [baseFiberOpen, le_fullFiberInterior_iff]
  constructor
  · intro h x hx
    obtain ⟨a, rfl⟩ := projection_surjective e x
    have ha : a ∈ E := hx.1
    have hb : A.hom a ∈ B := by
      rw [← invariantBaseMap_projection e a]
      exact hx.2
    exact h (show ((E).ι ≫ A.hom) ⟨a, ha⟩ ∈ B from hb)
  · intro h x hx
    apply h
    refine ⟨x.property, ?_⟩
    change (b).base (projection e x.val) ∈ B
    rw [invariantBaseMap_projection]
    exact hx

/-- A constructed base denominator yields a scalar on the unchanged original orbit domain. -/
theorem baseSection_principal_le_of_baseFiber (r : Γ(S, ⊤))
    (hr : S.basicOpen r ≤ baseFiberOpen e W O) :
    invariantPrincipal e W (invariantBaseSection e W r) ≤ O := by
  rw [invariantPrincipal_baseSection]
  exact (baseOpen_le_baseFiberOpen_iff e W O _).mp hr

/-- Over an affine base, every retained point has an actual original invariant denominator. -/
theorem exists_baseSection_principal [IsAffine S] (x : Orbit e) (hx : x ∈ W)
    (hb : (b).base x ∈ baseFiberOpen e W O) :
    ∃ r : Γ(S, ⊤), x ∈ invariantPrincipal e W (invariantBaseSection e W r) ∧
      invariantPrincipal e W (invariantBaseSection e W r) ≤ O := by
  obtain ⟨r, hr, hB⟩ := AffineEnvelopeFiniteNeighborhood.exists_envelope_principal
    (baseFiberOpen e W O) {(b).base x} (Set.finite_singleton _) (by simpa using hb)
  refine ⟨r, ?_, baseSection_principal_le_of_baseFiber e W O r hB⟩
  rw [invariantPrincipal_baseSection]
  exact ⟨hx, hr (Set.mem_singleton _)⟩

/-- One original scalar works simultaneously for any finite set of retained orbit points. -/
theorem exists_baseSection_finite_principal [IsAffine S]
    (s : Set (Orbit e)) (hs : s.Finite) (hW : s ⊆ W)
    (hB : ∀ x ∈ s, (b).base x ∈ baseFiberOpen e W O) :
    ∃ r : Γ(S, ⊤), s ⊆ invariantPrincipal e W (invariantBaseSection e W r) ∧
      invariantPrincipal e W (invariantBaseSection e W r) ≤ O := by
  obtain ⟨r, hr, hrB⟩ := AffineEnvelopeFiniteNeighborhood.exists_envelope_principal
    (baseFiberOpen e W O) ((b).base '' s) (hs.image _) (by
      rintro _ ⟨x, hx, rfl⟩
      exact hB x hx)
  refine ⟨r, ?_, baseSection_principal_le_of_baseFiber e W O r hrB⟩
  intro x hx
  rw [invariantPrincipal_baseSection]
  exact ⟨hW hx, hr (Set.mem_image_of_mem _ hx)⟩

/-- The retained orbit region is exactly the union of base-scalar neighborhoods inside O. -/
theorem baseFiberOpen_principal_cover [IsAffine S] :
    W ⊓ (Opens.map (b).base).obj (baseFiberOpen e W O) =
      ⨆ r : {r : Γ(S, ⊤) |
        invariantPrincipal e W (invariantBaseSection e W r) ≤ O},
        invariantPrincipal e W (invariantBaseSection e W r.val) := by
  apply le_antisymm
  · intro x hx
    obtain ⟨r, hr, hO⟩ := exists_baseSection_principal e W O x hx.1 hx.2
    exact Opens.mem_iSup.mpr ⟨⟨r, hO⟩, hr⟩
  · apply iSup_le
    intro r
    rw [invariantPrincipal_baseSection]
    exact inf_le_inf_left W ((Opens.map (b).base).monotone
      ((baseOpen_le_baseFiberOpen_iff e W O _).mpr (by
        rw [← invariantPrincipal_baseSection]
        exact r.property)))

end FLT.Mazur.RelativeRelationOrbit
