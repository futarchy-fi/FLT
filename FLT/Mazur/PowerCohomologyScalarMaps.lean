/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CohomologyImageReesModule

/-!
# Homogeneous scalars on the original power sheaves

A base ideal element of degree a acts from the n-th actual ideal power to
the (a+n)-th power. Cancellation against the original monic inclusions
proves the additive, unit and composition laws before taking cohomology.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry Opposite
open Scheme.Modules FLT.Mazur.FCurve FLT.Mazur.GlobalIdealPower
open FLT.Mazur.GlobalIdealPowerCompatibility FLT.Mazur.IdealPowerScalarLift

universe u

namespace FLT.Mazur.IdealAdicQuotient

variable {X : Scheme.{u}} [IsLocallyNoetherian X]
  {R : Type u} [CommRing R] (ρ : R →+* Γ(X, ⊤))
  (I : X.IdealSheafData) (M : X.Modules) [M.IsFinitePresentation]
  (J : Ideal R)
  (hJ : ∀ r : R, r ∈ J → ∀ U : X.affineOpens,
    X.presheaf.map U.1.leTop.op (ρ r) ∈ I.ideal U)

/-- Reindex the original ideal-power sheaf by equality of exponents. -/
@[irreducible]
def powerReindex {a b : ℕ} (h : a = b) : power I a M ⟶ power I b M :=
  transition I M h.symm.le

/-- Equality of exponents transports the original inclusion unchanged. -/
@[reassoc (attr := simp)]
lemma powerTransport_inclusion {a b : ℕ} (h : a = b) :
    powerReindex I M h ≫ inclusion (I ^ b) M =
      inclusion (I ^ a) M := by
  unfold powerReindex
  exact transition_comp I M h.symm.le

/-- Reindexing by reflexivity is the identity of the original power. -/
lemma powerReindex_refl (n : ℕ) : powerReindex I M (rfl : n = n) = 𝟙 (power I n M) := by
  apply (cancel_mono (inclusion (I ^ n) M)).mp
  exact (powerTransport_inclusion I M rfl).trans (Category.id_comp _).symm

include hJ in
/-- Affine multiplication lands in the actual summed ideal power. -/
lemma powerScalarMap_range (a n : ℕ) (r : ↥(J ^ a)) (U : X.affineOpens) :
    LinearMap.range ((scalarEnd (power I n M) (ρ r) ≫ inclusion (I ^ n) M).val.app
      (op U.1)).hom ≤ LinearMap.range ((inclusion (I ^ (a + n)) M).val.app (op U.1)).hom := by
  rintro _ ⟨x, rfl⟩
  rw [inclusion_range]
  change (inclusion (I ^ n) M).val.app (op U.1)
    (X.presheaf.map U.1.leTop.op (ρ r) • x) ∈ _
  rw [((inclusion (I ^ n) M).val.app (op U.1)).hom.map_smul]
  have hx : (inclusion (I ^ n) M).val.app (op U.1) x ∈
      (I ^ n).ideal U • (⊤ : Submodule Γ(X, U.1) Γ(M, U.1)) := by
    rw [← inclusion_range]
    exact ⟨x, rfl⟩
  have h := Submodule.smul_mem_smul (basePowerScalar_mem ρ I J hJ a r r.property U) hx
  change _ ∈ (I.ideal U) ^ (a + n) • (⊤ : Submodule Γ(X, U.1) Γ(M, U.1))
  rw [pow_add, Submodule.mul_smul]
  exact h

/-- A homogeneous base scalar acts on the actual ideal-power sheaf. -/
@[irreducible]
def powerScalarMap (a n : ℕ) (r : ↥(J ^ a)) :
    power I n M ⟶ power I (a + n) M :=
  affineFactor (scalarEnd (power I n M) (ρ r) ≫ inclusion (I ^ n) M)
    (inclusion (I ^ (a + n)) M) (powerScalarMap_range ρ I M J hJ a n r)

/-- The homogeneous action factors the original scalar multiplication. -/
lemma powerScalarMap_inclusion (a n : ℕ) (r : ↥(J ^ a)) :
    powerScalarMap ρ I M J hJ a n r ≫ inclusion (I ^ (a + n)) M =
      scalarEnd (power I n M) (ρ r) ≫ inclusion (I ^ n) M := by
  unfold powerScalarMap
  exact affineFactor_comp _ _ _

omit [IsLocallyNoetherian X] in
/-- Scalar multiplication commutes with every map of module sheaves. -/
@[reassoc]
lemma scalarEnd_naturality {N P : X.Modules} (g : N ⟶ P) (r : Γ(X, ⊤)) :
    scalarEnd N r ≫ g = g ≫ scalarEnd P r := by
  ext U x
  exact (g.val.app (op U)).hom.map_smul _ _

/-- Addition of homogeneous scalars is addition of the actual lifted maps. -/
lemma powerScalarMap_add (a n : ℕ) (r s : ↥(J ^ a)) :
    powerScalarMap ρ I M J hJ a n (r + s) =
      powerScalarMap ρ I M J hJ a n r + powerScalarMap ρ I M J hJ a n s := by
  apply (cancel_mono (inclusion (I ^ (a + n)) M)).mp
  simp only [Preadditive.add_comp, powerScalarMap_inclusion]
  ext U x
  change (inclusion (I ^ n) M).app U
      (X.presheaf.map U.leTop.op (ρ (r + s)) • x) =
    (inclusion (I ^ n) M).app U (X.presheaf.map U.leTop.op (ρ r) • x) +
      (inclusion (I ^ n) M).app U (X.presheaf.map U.leTop.op (ρ s) • x)
  rw [map_add, map_add, add_smul, map_add]

omit [IsLocallyNoetherian X] in
/-- Scalar multiplication by one is the identity of every module sheaf. -/
lemma scalarEnd_one (N : X.Modules) : scalarEnd N (1 : Γ(X, ⊤)) = 𝟙 N := by
  ext U x
  change X.presheaf.map U.leTop.op 1 • x = x
  rw [map_one, one_smul]

omit [IsLocallyNoetherian X] in
/-- Composition of scalar maps is multiplication of their global coefficients. -/
lemma scalarEnd_mul (N : X.Modules) (r s : Γ(X, ⊤)) :
    scalarEnd N r ≫ scalarEnd N s = scalarEnd N (s * r) := by
  ext U x
  change X.presheaf.map U.leTop.op s • (X.presheaf.map U.leTop.op r • x) =
    X.presheaf.map U.leTop.op (s * r) • x
  rw [map_mul, smul_smul]

/-- The degree-zero unit is the canonical equality transport. -/
lemma powerScalarMap_one (n : ℕ) :
    powerScalarMap ρ I M J hJ 0 n ⟨1, by simp⟩ =
      powerReindex I M (Nat.zero_add n).symm := by
  apply (cancel_mono (inclusion (I ^ (0 + n)) M)).mp
  exact (powerScalarMap_inclusion ρ I M J hJ 0 n _).trans
    ((congrArg (fun z ↦ scalarEnd (power I n M) z ≫ inclusion (I ^ n) M)
      (ρ.map_one)).trans
      ((congrArg (fun g ↦ g ≫ inclusion (I ^ n) M) (scalarEnd_one (power I n M))).trans
        ((Category.id_comp _).trans
          (powerTransport_inclusion I M (Nat.zero_add n).symm).symm)))

/-- Products of homogeneous scalars compose on the original power sheaves. -/
lemma powerScalarMap_mul (a b n : ℕ) (r : ↥(J ^ a)) (s : ↥(J ^ b)) :
    powerScalarMap ρ I M J hJ b n s ≫ powerScalarMap ρ I M J hJ a (b + n) r =
      powerScalarMap ρ I M J hJ (a + b) n
        ⟨r * s, by simpa only [pow_add] using Ideal.mul_mem_mul r.property s.property⟩ ≫
      powerReindex I M (Nat.add_assoc a b n) := by
  apply (cancel_mono (inclusion (I ^ (a + (b + n))) M)).mp
  rw [Category.assoc, powerScalarMap_inclusion, ← Category.assoc,
    ← scalarEnd_naturality, Category.assoc, powerScalarMap_inclusion,
    Category.assoc, powerTransport_inclusion I M (Nat.add_assoc a b n),
    powerScalarMap_inclusion]
  rw [← Category.assoc, scalarEnd_mul, map_mul, mul_comm]

end FLT.Mazur.IdealAdicQuotient
