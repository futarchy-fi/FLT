/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.PrincipalOpenNormalization
public import FLT.Mazur.WeierstrassDilatationResidueBoundaryFunctions
public import FLT.Mazur.WeierstrassDilatationHorizontalCongruence
public import FLT.Mazur.PolygonNodeDifferenceOpen
public import FLT.Mazur.PolygonAtlasSmoothLocus
public import Mathlib.AlgebraicGeometry.Noetherian

/-!
# The entire divided horizontal residue open is smooth below middle depth

The tensor of the original horizontal localization is the localization of
the normalized node at its tangent-coordinate difference. The two punctured
Laurent branches cover this full open, so its structure morphism is smooth.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory IsLocalRing
open scoped TensorProduct
namespace FLT.Mazur.WeierstrassDilatation
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u

/-- A principal node open covered by the two punctured branches is smooth over the field. -/
theorem nodePrincipalStructure_smooth {F : Type u} [Field F]
    (z : PolygonNodeEqualizer.A (R := F))
    (hz : Set.range (PolygonNodeBranches.left F) ∪ Set.range (PolygonNodeBranches.right F) =
      (PrimeSpectrum.basicOpen z : Set (PrimeSpectrum (PolygonNodeEqualizer.A (R := F))))) :
    Smooth (Spec.map (CommRingCat.ofHom (R := F) (S := Localization.Away z)
      (algebraMap F (Localization.Away z)))) := by
  let i : Spec (.of (Localization.Away z)) ⟶ PolygonNodeBranches.node F :=
    Spec.map (CommRingCat.ofHom (algebraMap _ (Localization.Away z)))
  let _ : IsOpenImmersion i := IsOpenImmersion.of_isLocalization z
  have hg : i ≫ PolygonNodeBranches.toBase F =
      Spec.map (CommRingCat.ofHom (R := F) (S := Localization.Away z)
      (algebraMap F (Localization.Away z))) := by
    rw [PolygonNodeBranches.toBase, ← Spec.map_comp]
    rfl
  rw [← hg, ← Scheme.Hom.smoothLocus_eq_top_iff, ← top_le_iff]
  intro x _
  apply (PolygonAtlas.mem_smooth_iff i (PolygonNodeBranches.toBase F) x).mp
  have hx : i x ∈ Set.range (PolygonNodeBranches.left F) ∪
      Set.range (PolygonNodeBranches.right F) := by
    rw [hz, ← PrimeSpectrum.localization_away_comap_range (Localization.Away z) z]
    exact ⟨x, rfl⟩
  rcases hx with ⟨y, hy⟩ | ⟨y, hy⟩
  · rw [← hy]
    apply (PolygonAtlas.mem_smooth_iff (PolygonNodeBranches.left F)
      (PolygonNodeBranches.toBase F) y).mpr
    rw [Scheme.Hom.smoothLocus_eq_top]
    trivial
  · rw [← hy]
    apply (PolygonAtlas.mem_smooth_iff (PolygonNodeBranches.right F)
      (PolygonNodeBranches.toBase F) y).mpr
    rw [Scheme.Hom.smoothLocus_eq_top]
    trivial

variable {R : Type u} [CommRing R] [IsDomain R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} {depth : ℕ} (D : SplitNodeDepth W π depth)
  (k : ℕ) (hk0 : 0 < k) (hk : 2 * k ≤ depth) (b3 b4 b6 : R)
  (h3 : W.a₃ = π ^ k * b3) (h4 : W.a₄ = π ^ k * b4)
  (h6 : W.a₆ = (π ^ k) ^ 2 * b6) (hp : 2 * k < depth)
local notation "F" => ResidueField R
local notation "x" => WeierstrassDilatation.x W (π ^ k) b3 b4 b6
local notation "tx" => tensorX W (π ^ k) b3 b4 b6 F
local notation "e" => residuePolygonEquiv D k hk0 hk b3 b4 b6 h3 h4 h6 hp
local notation "B" => HorizontalCoordinate W (π ^ k) b3 b4 b6

/-- The full original tensor horizontal boundary is the normalized node principal open. -/
def residueHorizontalEquiv : F ⊗[R] B ≃ₐ[F] Localization.Away ((e) tx) :=
  (PrincipalOpenTensor.equiv F x).trans (PrincipalOpenNormalization.equiv e tx)

include D hk0 hk h3 h4 h6 hp in
/-- Every point of the entire original horizontal residue tensor is smooth. -/
theorem residueHorizontalStructure_smooth :
    Smooth (Spec.map (CommRingCat.ofHom (algebraMap F (F ⊗[R] B)))) := by
  have hz : Set.range (PolygonNodeBranches.left F) ∪
      Set.range (PolygonNodeBranches.right F) =
        (PrimeSpectrum.basicOpen ((e) tx) :
          Set (PrimeSpectrum (PolygonNodeEqualizer.A (R := F)))) := by
    rw [residuePolygonEquiv_x]
    exact PolygonNodeBranches.branches_cover_difference (residueTangentUnit D)⁻¹
  let _ := nodePrincipalStructure_smooth ((e) tx) hz
  let E := Scheme.Spec.mapIso (RingEquiv.toCommRingCatIso
    (R := F ⊗[R] B) (S := Localization.Away ((e) tx))
    (residueHorizontalEquiv D k hk0 hk b3 b4 b6 h3 h4 h6 hp).toRingEquiv).op
  have he : E.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap F (F ⊗[R] B))) =
      Spec.map (CommRingCat.ofHom (algebraMap F (Localization.Away ((e) tx)))) :=
    algebraSpecIso_structure _
  have hs : Spec.map (CommRingCat.ofHom (algebraMap F (F ⊗[R] B))) =
      E.inv ≫ Spec.map (CommRingCat.ofHom (algebraMap F (Localization.Away ((e) tx)))) := by
    rw [← he, ← Category.assoc, E.inv_hom_id, Category.id_comp]
  rw [hs]
  infer_instance

end FLT.Mazur.WeierstrassDilatation
