/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GaloisRepresentation.Extensions.ContinuousH2Comparison
public import FLT.Mathlib.RepresentationTheory.Homological.ContCohomology.CupProduct

/-!
# The homogeneous cup with a trivial additive character

The scalar pairing is an actual continuous intertwining map. Its homogeneous
(1,1) cup is the homogenization of the explicit cup `d(h) • c(g)`.
-/

@[expose] public section

namespace GaloisRepresentation.Extensions

universe u

open ContRepresentation ContinuousCohomology ContinuousLinearMap.CompactOpen

variable {k G M : Type u} [Field k] [TopologicalSpace k] [DiscreteTopology k]
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [AddCommGroup M] [Module k M] [DistribMulAction G M] [SMulCommClass G k M]
    [TopologicalSpace M] [DiscreteTopology M] [ContinuousSMul G M] [ContinuousSMul k M]

/-- Scalar evaluation, as a continuous equivariant bilinear pairing. -/
def scalarCupPairing : coefficientRepresentation k G M →ⁱL
    (ContRepresentation.trivial k G k).linHom (coefficientRepresentation k G M) where
  toFun m :=
    { toFun := fun a ↦ a • m
      map_add' := fun a b ↦ add_smul a b m
      map_smul' := fun a b ↦ mul_smul a b m
      cont := continuous_of_discreteTopology }
  map_add' m n := by
    apply ContinuousLinearMap.ext
    intro a
    exact smul_add a m n
  map_smul' a m := by
    apply ContinuousLinearMap.ext
    intro b
    exact smul_comm b a m
  cont := continuous_of_discreteTopology
  isIntertwining' g := by
    apply ContinuousLinearMap.ext
    intro m
    apply ContinuousLinearMap.ext
    intro a
    change a • (g • m) = g • (a • m)
    exact (smul_comm g a m).symm

omit [IsTopologicalGroup G] in
/-- Joint continuity of the scalar pairing. -/
theorem scalarCupPairing_continuous :
    Continuous (fun p : M × k ↦ scalarCupPairing (G := G) p.1 p.2) :=
  continuous_of_discreteTopology

/-- A trivial additive character as a homogeneous one-cochain. -/
def trivialHomogeneousOne (d : ContinuousAddCharacter G k) :
    (TopRep.homogeneousCochains (TopRep.of (ContRepresentation.trivial k G k))).X 1 :=
  ⟨(⟨fun z : G × G ↦ d.1 (z.1⁻¹ * z.2), by fun_prop⟩ : C(G × G, k)).curry, by
    intro g
    ext x y
    change d.1 ((g⁻¹ * x)⁻¹ * (g⁻¹ * y)) = d.1 (x⁻¹ * y)
    simp [mul_assoc]⟩

/-- The homogeneous character lies in the actual degree-one kernel. -/
theorem trivialHomogeneousOne_cocycle (d : ContinuousAddCharacter G k) :
    (TopRep.homogeneousCochains (TopRep.of (ContRepresentation.trivial k G k))).d 1 2
      (trivialHomogeneousOne d) = 0 := by
  apply Subtype.ext
  ext g h j
  change d.1 (h⁻¹ * j) - (d.1 (g⁻¹ * j) - d.1 (g⁻¹ * h)) = 0
  have hd := d.2 (g⁻¹ * h) (h⁻¹ * j)
  simp only [mul_assoc, mul_inv_cancel_left] at hd
  rw [hd]
  abel

/-- A character as a homogeneous kernel representative. -/
def trivialOneCocycle (d : ContinuousAddCharacter G k) :
    TopModuleCat.ker
      ((TopRep.homogeneousCochains (TopRep.of (ContRepresentation.trivial k G k))).d 1 2) :=
  ⟨trivialHomogeneousOne d, trivialHomogeneousOne_cocycle d⟩

/-- The actual continuous degree-one cohomology class of a trivial character. -/
noncomputable def trivialH1Class (d : ContinuousAddCharacter G k) :
    continuousCohomology 1 (TopRep.of (ContRepresentation.trivial k G k)) :=
  (cohomologyIsoQuot _ 1).inv (TopModuleCat.cokerπ (bdryKer _ 1) (trivialOneCocycle d))

/-- The actual homogeneous cup has exactly the explicit inhomogeneous formula. -/
theorem homogeneousCup_eq (c : ContinuousCocycle G M) (d : ContinuousAddCharacter G k) :
    cupCochain (scalarCupPairing (G := G) (M := M)) scalarCupPairing_continuous
      1 1 2 rfl (homogeneousOne c.1) (trivialHomogeneousOne d) =
        homogeneousTwo (continuousCup c d) := by
  apply Subtype.ext
  rw [cupCochain_coe]
  ext g h j
  change d.1 (h⁻¹ * j) • (g • c.1 (g⁻¹ * h)) =
    g • (d.1 (h⁻¹ * j) • c.1 (g⁻¹ * h))
  exact (smul_comm g (d.1 (h⁻¹ * j)) (c.1 (g⁻¹ * h))).symm

end GaloisRepresentation.Extensions
