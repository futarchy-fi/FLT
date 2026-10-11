/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineHilbertRelationNeighborhoods

/-!
# Affine neighborhoods preserved by original relation inversion

The actual relation is separated because it embeds openly into an affine
product. Intersecting an affine neighborhood with its inverse image under
inversion therefore stays affine and is preserved by inversion. In particular
both complete endpoint fibers have such a common symmetric neighborhood.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart.AffineRestriction
open CartierAbel SchemePicard FCurve
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R] {X : Scheme}
  (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  (d : ℕ) (V : Over (Spec (.of R))) [IsAffine V.left]
  (c : (relativeFppfSheaf f).obj.obj (op V))
  {A : Over (Spec (.of R))} [IsAffine A.left] (k : A ⟶ variableHilbertTest f d V)
  [IsOpenImmersion k.left]
local notation "Z" => relation f hL d V c k
local notation "p" => fst f hL d V c k
local notation "q" => snd f hL d V c k

/-- The original full restricted relation is separated, using its actual affine envelope. -/
instance relation_isSeparated : (relation f hL d V c k).left.IsSeparated := by
  let _ := variableHilbertOverlap_envelope_affine V A
  refine ⟨?_⟩
  rw [← terminal.comp_from (toEnvelope f hL d V c k).left]
  infer_instance

/-- Inversion as an isomorphism of the underlying original relation scheme. -/
def inverseSchemeIso : (Z).left ≅ (Z).left := (Over.forget _).mapIso (swapIso f hL d V c k)

omit [IsAffine A.left] [IsAffine V.left] [IsOpenImmersion k.left] in
/-- Original inversion is involutive as a scheme morphism. -/
theorem inverseSchemeIso_involutive :
    (inverseSchemeIso f hL d V c k).hom ≫ (inverseSchemeIso f hL d V c k).hom = 𝟙 _ :=
  (inverseSchemeIso f hL d V c k).hom_inv_id

/-- Inverse-stable finite sets have inverse-stable affine neighborhoods inside any given open. -/
theorem exists_symmetric_affine_neighborhood (s : Set (Z).left) (hs : s.Finite)
    (hi : (inverseSchemeIso f hL d V c k).hom '' s ⊆ s)
    (W : (Z).left.Opens) (hsW : s ⊆ W) :
    ∃ U : (Z).left.Opens, IsAffineOpen U ∧ s ⊆ U ∧ U ≤ W ∧
      (inverseSchemeIso f hL d V c k).hom ⁻¹ᵁ U = U := by
  obtain ⟨B, hB, hsB, hBW⟩ := exists_affine_neighborhood f hL d V c k W s hs hsW
  let e := inverseSchemeIso f hL d V c k
  refine ⟨B ⊓ e.hom ⁻¹ᵁ B, hB.inf (hB.preimage_of_isIso e.hom),
    (fun z hz ↦ ⟨hsB hz, hsB (hi (Set.mem_image_of_mem e.hom hz))⟩),
    inf_le_left.trans hBW, ?_⟩
  rw [Scheme.Hom.preimage_inf, ← Scheme.Hom.comp_preimage,
    inverseSchemeIso_involutive, Scheme.Hom.id_preimage, inf_comm]

omit [IsAffine A.left] [IsAffine V.left] [IsOpenImmersion k.left] in
/-- Inversion preserves the union of the two complete original endpoint fibers. -/
theorem inverse_endpoint_fibers (x : A.left) :
    (inverseSchemeIso f hL d V c k).hom ''
      ((p).left ⁻¹' {x} ∪ (q).left ⁻¹' {x}) ⊆ (p).left ⁻¹' {x} ∪ (q).left ⁻¹' {x} := by
  rintro _ ⟨z, hz, rfl⟩
  rcases hz with hz | hz
  · right
    change (((equivalence f hL d V c k).s ≫ q).left z) = x
    rw [(equivalence f hL d V c k).symmetry₂]
    exact hz
  · left
    change (((equivalence f hL d V c k).s ≫ p).left z) = x
    rw [(equivalence f hL d V c k).symmetry₁]
    exact hz

/-- Both full endpoint fibers have one affine neighborhood preserved by original inversion. -/
theorem exists_symmetric_endpoint_neighborhood [Etale V.hom] (x : A.left)
    (W : (Z).left.Opens) (hW : (p).left ⁻¹' {x} ∪ (q).left ⁻¹' {x} ⊆ W) :
    ∃ U : (Z).left.Opens, IsAffineOpen U ∧
      (p).left ⁻¹' {x} ∪ (q).left ⁻¹' {x} ⊆ U ∧ U ≤ W ∧
        (inverseSchemeIso f hL d V c k).hom ⁻¹ᵁ U = U :=
  exists_symmetric_affine_neighborhood f hL d V c k _
    ((fst_finite_fiber f hL d V c k x).union (snd_finite_fiber f hL d V c k x))
    (inverse_endpoint_fibers f hL d V c k x) W hW

end FLT.Mazur.HilbertChart.AffineRestriction
