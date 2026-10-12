/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertBoundedPolynomialTower
public import FLT.Mazur.HilbertFamilyGrassmannianSchemeMap
public import FLT.Mazur.HilbertFamilyGrassmannianNaturality
public import FLT.Mazur.GrassmannianScalarExtensionTransport

/-!
# Naturality in the original bounded polynomial ambient

The full ideal's Grassmannian point is natural in the coefficient algebra,
using the original base ring throughout the ambient coordinate comparison.
-/

@[expose] public noncomputable section
open TensorProduct
namespace FLT.Mazur.HilbertChart
open GrassmannianChart
set_option backward.isDefEq.respectTransparency false
universe u
variable (R S T I : Type u) [CommRing R] [CommRing S] [CommRing T]
  [Algebra R S] [Algebra S T] [Algebra R T] [IsScalarTower R S T]

/-- Inverse bounded ambient coordinates commute with arbitrary coefficient extension. -/
theorem boundedPolynomialBaseChangeEquiv_rechart (n : ℕ) :
    ((boundedPolynomialBaseChangeEquiv R S I n).symm.baseChange S T).trans
        (AlgebraTensorModule.cancelBaseChange R S T T
          (MvPolynomial.restrictTotalDegree I R n)) =
      (boundedPolynomialBaseChangeEquiv S T I n).trans
        (boundedPolynomialBaseChangeEquiv R T I n).symm := by
  ext x
  apply (boundedPolynomialBaseChangeEquiv R T I n).injective
  have h := congrArg
    (fun e ↦ e (((boundedPolynomialBaseChangeEquiv R S I n).baseChange S T).symm x))
    (boundedPolynomialBaseChangeEquiv_tower R S T I n)
  simpa only [LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply,
    LinearEquiv.baseChange_symm] using h.symm

variable (J : Ideal (MvPolynomial I S)) (d : ℕ)
  [Module.FinitePresentation S (MvPolynomial I S ⧸ J)]
  [Module.Flat S (MvPolynomial I S ⧸ J)]
  (hd : ∀ p : PrimeSpectrum S, Module.finrank p.asIdeal.ResidueField
    (MvPolynomial I p.asIdeal.ResidueField ⧸
      J.map (MvPolynomial.map (algebraMap S p.asIdeal.ResidueField))) = d)

local instance hilbertAmbientExtendedFinitePresentation : Module.FinitePresentation T
    (MvPolynomial I T ⧸ J.map (MvPolynomial.map (algebraMap S T))) :=
  polynomialQuotient_finitePresentation_baseChange I S J T
local instance hilbertAmbientExtendedFlat : Module.Flat T
    (MvPolynomial I T ⧸ J.map (MvPolynomial.map (algebraMap S T))) :=
  polynomialQuotient_flat_baseChange I S J T

/-- The actual Grassmannian functor extends exactly the original full family's relations. -/
theorem finiteFlatHilbertAmbientPoint_natural :
    Module.Grassmannian.map (IsScalarTower.toAlgHom R S T)
        (finiteFlatHilbertAmbientPoint R S I J d hd) =
      finiteFlatHilbertAmbientPoint R T I (J.map (MvPolynomial.map (algebraMap S T))) d
        (polynomialQuotient_residueRank_baseChange I S J T d hd) := by
  rw [grassmannian_map_scalarExtension]
  unfold finiteFlatHilbertAmbientPoint
  rw [grassmannianScalarExtension_transport, boundedPolynomialBaseChangeEquiv_rechart,
    ← ambientTransportPoint_scalarExtension, finiteFlatGrassmannianParameter_natural]
  rfl

end FLT.Mazur.HilbertChart
