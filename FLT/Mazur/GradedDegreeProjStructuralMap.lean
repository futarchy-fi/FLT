/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GradedDegreeProjMap
public import FLT.Mazur.GradedProjStructuralMap

/-!
# Degree-changing Proj maps retain the structural base

Compatibility with scalars passes through the actual homogeneous fractions
and then through the covering affine charts of the global morphism.
-/

@[expose] public noncomputable section
open HomogeneousLocalization AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.GradedDegreeProjStructuralMap
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra R B]
  (𝒜 : ℕ → Submodule R A) (ℬ : ℕ → Submodule R B) [GradedAlgebra 𝒜] [GradedAlgebra ℬ]
  (f : A →+* B) (r : ℕ) (hf : ∀ d a, a ∈ 𝒜 d → f a ∈ ℬ (r * d))
  (hR : ∀ a, f (algebraMap R A a) = algebraMap R B a)

include hR

/-- The original homogeneous fraction map preserves the structural scalar fractions. -/
theorem awayMap_scalar (s : A) :
    (GradedLocalizationDegreeMap.awayMap 𝒜 ℬ f r hf s).comp
        (GradedProjStructuralMap.scalarToAway 𝒜 s) =
      GradedProjStructuralMap.scalarToAway ℬ (f s) := by
  apply RingHom.ext
  intro a
  apply HomogeneousLocalization.val_injective
  change (GradedLocalizationDegreeMap.mapValue 𝒜 ℬ f r hf
    (by rintro _ ⟨k, rfl⟩; exact ⟨k, (map_pow f s k).symm⟩)
    (fromZeroRingHom 𝒜 _ (algebraMap R (𝒜 0) a))).val =
      (fromZeroRingHom ℬ _ (algebraMap R (ℬ 0) a)).val
  rw [GradedLocalizationDegreeMap.mapValue_val]
  change IsLocalization.map (Localization (.powers (f s))) f
    (by rintro _ ⟨k, rfl⟩; exact ⟨k, (map_pow f s k).symm⟩)
    (Localization.mk (algebraMap R A a) 1) = Localization.mk (algebraMap R B a) 1
  simp only [Localization.mk_eq_mk', IsLocalization.map_mk', hR, Submonoid.coe_one, map_one]
  rfl

/-- Every local degree-changing chart keeps the original scalar structural map. -/
@[reassoc]
theorem chartMap_toSpecBase {d : ℕ} (s : A) (hs : s ∈ 𝒜 d) (hd : 0 < d) :
    GradedDegreeProjOverlap.chartMap 𝒜 ℬ f r hf s hs hd ≫
        GradedProjStructuralMap.toSpecBase 𝒜 =
      Spec.map (CommRingCat.ofHom (GradedProjStructuralMap.scalarToAway ℬ (f s))) := by
  rw [GradedDegreeProjOverlap.chartMap, Category.assoc,
    GradedProjStructuralMap.awayι_toSpecBase, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
    awayMap_scalar 𝒜 ℬ f r hf hR]

/-- The global glued comparison commutes with the actual structural map. -/
@[reassoc]
theorem map_toSpecBase (hr : 0 < r)
    (hcover : (⨆ i : Σ d : PNat, 𝒜 d, Proj.basicOpen ℬ (f i.2)) = ⊤) :
    GradedDegreeProjMap.map 𝒜 ℬ f r hf hr hcover ≫ GradedProjStructuralMap.toSpecBase 𝒜 =
      GradedProjStructuralMap.toSpecBase ℬ := by
  apply (GradedDegreeProjMap.sourceCover 𝒜 ℬ f r hf hr hcover).openCover.hom_ext
  intro i
  change (Σ d : PNat, 𝒜 d) at i
  change Proj.awayι ℬ (f i.2) (hf _ _ i.2.property) (Nat.mul_pos hr i.1.property) ≫ _ =
    Proj.awayι ℬ (f i.2) (hf _ _ i.2.property) (Nat.mul_pos hr i.1.property) ≫ _
  rw [GradedDegreeProjMap.awayι_map_assoc 𝒜 ℬ f r hf hr hcover
    i.2 i.2.property i.1.property,
    chartMap_toSpecBase 𝒜 ℬ f r hf hR, GradedProjStructuralMap.awayι_toSpecBase]

end FLT.Mazur.GradedDegreeProjStructuralMap
