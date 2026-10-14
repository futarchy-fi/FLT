/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientShearSmoothOrbit
public import FLT.Mazur.WeierstrassCoefficientShearTransport
public import FLT.Mazur.WeierstrassSmoothFaithfulCoefficientDescent

/-!
# The retained full smooth orbit descends with its original embedding

The original smooth orbit is cartesian inside the complete equation model.
Its whole range, overlap transport, and unique integral embedding are retained.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (S : Type u) [CommRing S] [Algebra R S] (r : S) (j : ℕ) (hj : j ≤ n)
local notation "f" => integralSmoothStructure (W.map (algebraMap R S))
local notation "g" => coefficientShearGluedStructure hπ data S r j hj
local notation "p" => coefficientShearGluedProjection hπ data S r j hj
local notation "q" => Spec.map (CommRingCat.ofHom (algebraMap R S))
local notation "B" => coefficientShearSmoothEmbedding hπ data S r j hj
local notation "B₀" => finiteGlobalSmoothEmbedding hπ data j hj
local notation "U" => originalSmoothCoefficientMap S W

/-- The entire sheared smooth orbit projects to the actual integral smooth embedding. -/
@[reassoc] theorem coefficientShearSmoothEmbedding_projection : B ≫ p = U ≫ B₀ := by
  rw [coefficientShearGluedProjection, coefficientShearSmoothEmbedding_reconstruction_assoc,
    finiteGlobalSmoothCoefficientEmbedding_projection]

/-- The smooth orbit in the full equation gluing is the actual inverse image of the original. -/
theorem coefficientShearSmoothEmbedding_isPullback : IsPullback U B B₀ p := by
  apply IsPullback.of_bot _ (coefficientShearSmoothEmbedding_projection
    hπ data S r j hj).symm (coefficientShearGlued_isPullback hπ data S r j hj).flip
  simpa only [coefficientShearSmoothEmbedding_structure,
    finiteGlobalSmoothEmbedding_structure] using originalSmoothCoefficientMap_isPullback S W

/-- No extra equation-model points lie over the whole original smooth orbit. -/
theorem coefficientShearSmoothEmbedding_range : Set.range B = p ⁻¹' Set.range B₀ := by
  ext z
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨U a, (congrArg (fun k => k a)
      (coefficientShearSmoothEmbedding_projection hπ data S r j hj)).symm⟩
  · rintro ⟨a, ha⟩
    obtain ⟨b, _, hb⟩ := Scheme.exists_preimage_of_isPullback
      (coefficientShearSmoothEmbedding_isPullback hπ data S r j hj) a z ha
    exact ⟨b, hb⟩

variable {T : Scheme.{u}} (a b : T ⟶ Spec (.of S))
  (h : a ≫ Spec.map (CommRingCat.ofHom (algebraMap R S)) =
    b ≫ Spec.map (CommRingCat.ofHom (algebraMap R S)))

/-- Full smooth overlap transport intertwines the independently constructed smooth embedding. -/
@[reassoc] theorem coefficientShearSmoothEmbedding_transport :
    (CartesianCoefficientTransport.iso (originalSmoothCoefficientMap_isPullback S W)
        a b h).hom ≫
      CartesianCoefficientTransport.objectMap b B
        (coefficientShearSmoothEmbedding_structure hπ data S r j hj) =
    CartesianCoefficientTransport.objectMap a B
        (coefficientShearSmoothEmbedding_structure hπ data S r j hj) ≫
      (coefficientShearTransport hπ data S r j hj a b h).hom :=
  CartesianCoefficientTransport.map_naturality
    (originalSmoothCoefficientMap_isPullback S W) a b h
    (coefficientShearGlued_isPullback hπ data S r j hj).flip B B₀
    (coefficientShearSmoothEmbedding_projection hπ data S r j hj)
    (coefficientShearSmoothEmbedding_structure hπ data S r j hj)

omit a b h in
/-- Faithful coefficients recover exactly one integral embedding of the full smooth orbit. -/
theorem coefficientShearSmoothEmbedding_unique (hS : (algebraMap R S).FaithfullyFlat) :
    ∃! t : (integralSmoothOpen W).toScheme ⟶ finiteGlobalModel hπ data j hj,
      U ≫ t = B ≫ p := by
  let _ := originalSmoothCoefficientMap_epi_of_faithfullyFlat S W hS
  refine ⟨B₀, (coefficientShearSmoothEmbedding_projection hπ data S r j hj).symm, ?_⟩
  intro t ht
  exact (cancel_epi U).mp
    (ht.trans (coefficientShearSmoothEmbedding_projection hπ data S r j hj))

end FLT.Mazur.WeierstrassDividedDepth
