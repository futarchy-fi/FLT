/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDilatationZeroResidueGeometry
public import FLT.Mazur.WeierstrassSplitNodalFieldSmooth
public import FLT.Mazur.PolygonAtlasSmoothLocus

/-!
# Smooth points of the original zero-depth divided chart have nonzero ordinate

The full nodal comparison preserves the original tensor Y function and the
ambient structure map. Thus its smooth points lie in the original Y-open.
-/

@[expose] public noncomputable section
open IsLocalRing AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDilatation
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} {depth : ℕ} (D : SplitNodeDepth W π depth)
  (hdepth : 0 < depth) (k : ℕ) (hk : k = 0) (b3 b4 b6 : R)
  (h3 : W.a₃ = π ^ k * b3) (h4 : W.a₄ = π ^ k * b4)
  (h6 : W.a₆ = (π ^ k) ^ 2 * b6)
local notation "F" => ResidueField R
local notation "N" => WeierstrassIntegralChart.splitNodalEquation (residueTangentUnit D)
local notation "C" => WeierstrassIntegralChart.Coordinate N 2
local notation "T" => ScalarExtension W (π ^ k) b3 b4 b6 F
local notation "E" => zeroResidueNodalIso D hdepth k hk b3 b4 b6 h3 h4 h6

variable {X : Scheme.{u}}
  (g : Spec (.of (ScalarExtension W (π ^ k) b3 b4 b6 (ResidueField R))) ⟶ X)
  [IsOpenImmersion g] (p : X ⟶ Spec (.of (ResidueField R)))
  [LocallyOfFinitePresentation p]
  (hg : g ≫ p = Spec.map (CommRingCat.ofHom (algebraMap (ResidueField R)
    (ScalarExtension W (π ^ k) b3 b4 b6 (ResidueField R)))))

include D hdepth hk h3 h4 h6 hg in
/-- Every smooth point of the original zero-depth divided tensor chart has invertible Y locally. -/
theorem zeroResidue_smooth_y (z : Spec (.of T)) (hz : g z ∈ p.smoothLocus) :
    tensorY W (π ^ k) b3 b4 b6 F ∉ z.asIdeal := by
  obtain ⟨v, rfl⟩ := (E).hom.homeomorph.surjective z
  have hs := PolygonAtlas.mem_smooth_iff ((E).hom ≫ g) p v
  have he : ((E).hom ≫ g) ≫ p =
      Spec.map (CommRingCat.ofHom (algebraMap F C)) := by
    rw [Category.assoc, hg, zeroResidueNodalIso_structure]
  simp only [he] at hs
  have hv : v ∈ (WeierstrassIntegralChart.chartStructure N 2).smoothLocus := hs.mp hz
  have hy := WeierstrassIntegralChart.splitNodalAffine_smooth_y (residueTangentUnit D) v hv
  change zeroResidueNodalEquiv D hdepth k hk b3 b4 b6 h3 h4 h6
    (tensorY W (π ^ k) b3 b4 b6 F) ∉ v.asIdeal
  rw [zeroResidueNodalEquiv_y]
  exact hy

end FLT.Mazur.WeierstrassDilatation
