/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSmoothDividedProductResidue
public import FLT.Mazur.WeierstrassSmoothDividedIntegralOutput
public import FLT.Mazur.WeierstrassSplitDepthSecantResidue

/-!
# The terminal product residue factors through the actual secant source

The original right input reduces to the node. The smooth affine/Y overlap
therefore constructs its secant factorization without an invertibility assumption.
-/

@[expose] public noncomputable section
open IsLocalRing
namespace FLT.Mazur.WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} {depth k : ℕ} (D : SplitNodeDepth W π depth)
  (d : WeierstrassDividedDepth.Data W π k) (hk0 : 0 < k) (hk : 2 * k ≤ depth)
  (hp : 2 * k = depth)
local notation "𝕂" => ResidueField R
local notation "C" => SmoothHorizontalResidueRing D
local notation "S" => SmoothDividedProductRing W (π ^ k) d.b3 d.b4 d.b6
local notation "T" => SmoothDividedSecantRing d
local notation "a" => smoothDividedLeft W (π ^ k) d.b3 d.b4 d.b6
local notation "c" => smoothDividedRight W (π ^ k) d.b3 d.b4 d.b6
  d.factor3 d.factor4 d.factor6
local notation "v" => smoothDividedY W (π ^ k) d.b3 d.b4 d.b6
local notation "e" => smoothDividedProductResidue D d hk0 hk hp

omit [IsDomain R] in
include hk0 in
/-- The scale vanishes in the actual independent residue parameter ring. -/
theorem smoothDividedResidue_scale : algebraMap R C (π ^ k) = 0 := by
  rw [IsScalarTower.algebraMap_apply R 𝕂 C, ResidueField.algebraMap_eq,
    WeierstrassDilatation.residue_scale_eq_zero D k hk0, map_zero]

/-- The contracted divided input has zero original abscissa on the residue product. -/
theorem smoothDividedProductResidue_node : e (c (coord W 2 0)) = 0 := by
  change e (algebraMap _ S
    (WeierstrassDilatation.fromOriginal W (π ^ k) d.b3 d.b4 d.b6
      d.factor3 d.factor4 d.factor6 (coord W 2 0))) = 0
  rw [WeierstrassDilatation.fromOriginal_x, map_mul, map_mul,
    ← IsScalarTower.algebraMap_apply, AlgHom.commutes,
    smoothDividedResidue_scale D hk0, zero_mul]

/-- The original terminal residue factors through the concrete ordinary secant open. -/
def smoothDividedSecantResidueRingHom : T →+* C :=
  splitDepthSecantResidue D (by omega) a c v
    (smoothDivided_common W (π ^ k) d.b3 d.b4 d.b6) (e).toRingHom
    (smoothDividedProductResidue_maximal D d hk0 hk hp)
    (smoothDividedProductResidue_node D d hk0 hk hp)

/-- The secant residue retains every function on the original integral product. -/
theorem smoothDividedSecantResidueRingHom_base (q : S) :
    smoothDividedSecantResidueRingHom D d hk0 hk hp (algebraMap S T q) = e q :=
  splitDepthSecantResidue_base ..

/-- Coefficient compatibility of the constructed secant residue map. -/
def smoothDividedSecantResidue : T →ₐ[R] C :=
  { smoothDividedSecantResidueRingHom D d hk0 hk hp with
    commutes' := fun r => by
      change smoothDividedSecantResidueRingHom D d hk0 hk hp (algebraMap R T r) = _
      rw [IsScalarTower.algebraMap_apply R S T, smoothDividedSecantResidueRingHom_base]
      exact (e).commutes r }

/-- Every original product function survives the coefficient-compatible residue factor. -/
theorem smoothDividedSecantResidue_base (q : S) :
    smoothDividedSecantResidue D d hk0 hk hp (algebraMap S T q) = e q :=
  smoothDividedSecantResidueRingHom_base D d hk0 hk hp q

/-- The actual secant factor kills the original maximal ideal. -/
theorem smoothDividedSecantResidue_maximal :
    (maximalIdeal R).map (algebraMap R T) ≤
      RingHom.ker (smoothDividedSecantResidue D d hk0 hk hp).toRingHom := by
  rw [Ideal.map_le_iff_le_comap]
  intro q hq
  change smoothDividedSecantResidue D d hk0 hk hp (algebraMap R T q) = 0
  rw [AlgHom.commutes, IsScalarTower.algebraMap_apply R 𝕂 C,
    ResidueField.algebraMap_eq, (residue_eq_zero_iff q).mpr hq, map_zero]

end FLT.Mazur.WeierstrassIntegralChart
