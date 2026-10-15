/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertBoundaryKernelPair
public import FLT.Mazur.ClosedRelationOrbitEmbedding

/-!
# The original closed boundary in the orbit quotient

The full closed relation gives exactly the closed complement of the original
full-interior orbits. This identifies the two strata topologically and retains
all original arrows; it does not glue schemes across their boundary.
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
  (d : ℕ) (V : Over (Spec (.of R))) [Etale V.hom]
  (c : (relativeFppfSheaf f).obj.obj (op V))
  {A : Over (Spec (.of R))} [IsAffine A.left]
  (k : A ⟶ variableHilbertTest f d V) [IsOpenImmersion k.left]
local notation "π" => Over.Hom.left (prod.fst : prod A V ⟶ A)
local notation "O" => Scheme.Hom.opensRange (Over.Hom.left (toEnvelope f hL d V c k))
local notation "B" => originalBoundarySource f hL d V c k
local notation "i" => originalBoundarySourceMap f hL d V c k
local notation "D" => relation f hL d V c k
local notation "p" => fst f hL d V c k
local notation "q" => snd f hL d V c k

local notation "C" => originalClosedRelation f hL d V c k
local notation "r" => originalClosedFst f hL d V c k
local notation "s" => originalClosedSnd f hL d V c k
local notation "z" => originalClosedArrow f hL d V c k

open RelativeRelationOrbit
local notation "e" => equivalence f hL d V c k
local notation "ec" => originalClosedEquivalence f hL d V c k

/-- The map of actual original orbits induced by the closed boundary inclusion. -/
def originalClosedOrbitMap : Orbit ec → Orbit e :=
  closedOrbitMap e ec i z (originalClosedArrow_fst f hL d V c k)
    (originalClosedArrow_snd f hL d V c k)

/-- The original source point is retained in the ambient orbit quotient. -/
theorem originalClosedOrbitMap_projection (x : (B).left) :
    originalClosedOrbitMap f hL d V c k (projection ec x) = projection e ((i).left x) := rfl

/-- The full closed quotient is a closed topological subspace of the original quotient. -/
theorem originalClosedOrbitMap_isClosedEmbedding :
    Topology.IsClosedEmbedding (originalClosedOrbitMap f hL d V c k) :=
  closedOrbitMap_isClosedEmbedding e ec i z (originalClosedArrow_fst f hL d V c k)
    (originalClosedArrow_snd f hL d V c k) (originalClosedFst_isPullback f hL d V c k)

omit [Etale V.hom] in
/-- The original closed source has precisely the complement of the full-interior carrier. -/
theorem originalBoundarySource_range :
    Set.range (i).left = (fullFiberInterior π O : Set A.left)ᶜ := by
  change Set.range (boundaryIdealSheaf π O).subschemeι = _
  rw [Scheme.IdealSheafData.range_subschemeι, boundaryIdealSheaf_support]
  change closure (π '' (O : Set (prod A V).left)ᶜ) =
    (interior (π '' (O : Set (prod A V).left)ᶜ)ᶜ)ᶜ
  rw [interior_compl, compl_compl]

/-- Pulling back the closed orbit image recovers the original closed boundary exactly. -/
theorem originalClosedOrbitMap_preimage_range :
    projection e ⁻¹' Set.range (originalClosedOrbitMap f hL d V c k) =
      (fullFiberInterior π O : Set A.left)ᶜ := by
  have h := closedOrbitMap_preimage_image e ec i z (originalClosedArrow_fst f hL d V c k)
    (originalClosedArrow_snd f hL d V c k) (originalClosedFst_isPullback f hL d V c k)
    Set.univ
  simpa only [originalClosedOrbitMap, Set.image_univ, Set.preimage_univ,
    originalBoundarySource_range] using h

/-- The closed orbit stratum is exactly complementary to the original full-interior orbits. -/
theorem originalClosedOrbitMap_range :
    Set.range (originalClosedOrbitMap f hL d V c k) =
      (projection e '' (fullFiberInterior π O : Set A.left))ᶜ := by
  ext v
  obtain ⟨x, rfl⟩ := projection_surjective e v
  have H (y : A.left) :
      projection e y ∈ Set.range (originalClosedOrbitMap f hL d V c k) ↔
        y ∉ (fullFiberInterior π O : Set A.left) :=
    Set.ext_iff.mp (originalClosedOrbitMap_preimage_range f hL d V c k) y
  constructor
  · intro hx
    rintro ⟨y, hy, he⟩
    exact (H y).mp (he.symm ▸ hx) hy
  · intro hx
    apply (H x).mpr
    exact fun hi ↦ hx ⟨x, hi, rfl⟩

end FLT.Mazur.HilbertChart.AffineRestriction
