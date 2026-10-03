/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.RaynaudScalarExtensionRigidity
public import FLT.GroupScheme.RaynaudUnramifiedOrder
public import FLT.GroupScheme.RaynaudStrictHenselian

/-!
# Scalar-filtered rigidity over a Henselian DVR

Construct the unramified strict-Henselian tower, preserve the ramification
bound and filtration there, and descend surjectivity by faithful flatness.
-/

@[expose] public noncomputable section
namespace ThreeAdicPlan
open IsLocalRing IsDiscreteValuationRing

variable {R K : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [HenselianLocalRing R] [Field K] [Algebra R K] [CharZero K] [IsFractionRing R K]
  (p : ℕ) [CharP (ResidueField R) p]

/-- A scalar filtration proves rigidity without assuming a separably closed residue field. -/
theorem ModelHom.surjective_of_henselian_scalarFiltration
    (he : RaynaudParameters.order (p : R) < p - 1)
    {n : ℕ} {X Y : FF R K} (hX : X.HasScalarFiltration p n)
    (g : ModelHom X Y) (hg : Function.Bijective (genericHom g)) : Function.Surjective g := by
  let : FaithfulSMul R (AlgebraicClosure K) :=
    (faithfulSMul_iff_algebraMap_injective R (AlgebraicClosure K)).mpr (by
      rw [IsScalarTower.algebraMap_eq R K (AlgebraicClosure K)]
      exact (algebraMap K (AlgebraicClosure K)).injective.comp (IsFractionRing.injective R K))
  obtain ⟨π, hπ⟩ := exists_irreducible R
  obtain ⟨A, hD, hH, hC, hI, hF, hLocal, hSep, hKL, hT, hAlg, hSepK, e, hπA, _, _⟩ :=
    RaynaudParameters.exists_strict_henselian_unramified_tower
      (K := K) (Ω := AlgebraicClosure K) hπ
  let := hD; let := hH; let := hC; let := hI; let := hF; let := hLocal
  let := hSep; let := hKL; let := hT; let := hAlg; let := hSepK
  let : CharZero (FractionRing A) := charZero_of_injective_algebraMap
    (algebraMap K (FractionRing A)).injective
  let : CharP (ResidueField A) p := charP_of_injective_algebraMap
    (algebraMap (ResidueField R) (ResidueField A)).injective p
  have hp : (p : R) ≠ 0 := by
    have : CharZero R := (algebraMap R K).charZero
    exact Nat.cast_ne_zero.mpr (by omega)
  have heA : RaynaudParameters.order (p : A) < p - 1 := by
    have h := RaynaudParameters.order_map_of_uniformizer (algebraMap R A) hπ hπA hp
    simpa only [map_natCast] using h.trans_lt he
  exact g.surjective_of_scalarFiltration_baseChange A (FractionRing A) p heA
    (hX.scalarExtension A (FractionRing A)) hg

end ThreeAdicPlan
