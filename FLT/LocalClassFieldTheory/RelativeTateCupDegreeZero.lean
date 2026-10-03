/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.RelativeFundamentalTateCup
public import FLT.LocalClassFieldTheory.TateScalarDegreeZero

/-!
# The degree-zero relative Tate cup is an isomorphism

The scalar unit generates actual Tate H⁰ and is killed by the group order.
The fundamental Tate H² class has that exact order and generates H². Since
actual cup sends the first generator to the second, it is bijective.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace LocalClassFieldTheory

open IsLocalRing CategoryTheory

variable (R S K C : Type)
  [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
  [Algebra R S] [Module.Finite R S] [FaithfulSMul R S]
  [Field K] [Algebra R K] [IsFractionRing R K]
  [Field C] [Algebra K C] [Algebra R C] [IsScalarTower R K C]
  (E : IntermediateField K C) [IsGalois K E]
  [Algebra S E] [IsFractionRing S E] [Algebra S C] [IsScalarTower S E C]
  [IsScalarTower R S E] [IsScalarTower R S C]
  [Algebra.IsSeparable K C] [IsSepClosed C]
  [Finite (ResidueField R)] [Finite (ResidueField S)]
  [IsAdicComplete (maximalIdeal R) R] [IsAdicComplete (maximalIdeal S) S]

local notation "A" => maximalUnramified R K C
local notation "B" => maximalUnramified S E C
local notation "N" => (MonoidHom.ker (AlgEquiv.restrictNormalHom E : Gal(C/K) →* Gal(E/K)))

attribute [local instance] relativeBaseTower unramifiedUnionGalois fieldUnitAction
  unramifiedFieldUnitTopology unramifiedFieldUnitDiscrete
  separableClosureGalois separableClosureUnitTopology separableClosureUnitDiscrete

variable [FiniteDimensional K E]

local notation "d" => Module.finrank K E

variable [TopologicalSpace (Additive Eˣ)] [DiscreteTopology (Additive Eˣ)]

variable [CharZero C] (p : ℕ) [Fact p.Prime] [CharP (ResidueField S) p]

/-- The cup normalization agrees with the proved cyclic coordinates on relative Tate H². -/
theorem relativeFundamentalTateCup_unit_generator :
    relativeFundamentalTateCup R S K C E 0 (tateScalarUnit ℤ Gal(E/K)) =
      relativeTateH2Equiv R S K C E p 1 :=
  (relativeFundamentalTateCup_unit R S K C E).trans
    (relativeTateH2Equiv_one R S K C E p).symm

include p in
/-- The genuine degree-zero relative fundamental cup is surjective. -/
theorem relativeFundamentalTateCup_zero_surjective :
    Function.Surjective (relativeFundamentalTateCup R S K C E 0).hom := by
  intro a
  obtain ⟨z, rfl⟩ := (relativeTateH2Equiv R S K C E p).surjective a
  obtain ⟨m, rfl⟩ := ZMod.intCast_surjective z
  refine ⟨m • tateScalarUnit ℤ Gal(E/K), ?_⟩
  rw [map_zsmul, relativeFundamentalTateCup_unit_generator R S K C E p]
  simpa using (map_zsmul (relativeTateH2Equiv R S K C E p) m (1 : ZMod d)).symm

include p in
/-- The genuine degree-zero relative fundamental cup is injective. -/
theorem relativeFundamentalTateCup_zero_injective :
    Function.Injective (relativeFundamentalTateCup R S K C E 0).hom := by
  apply (injective_iff_map_eq_zero _).mpr
  intro a ha
  obtain ⟨m, rfl⟩ := tateScalarUnit_generates Gal(E/K) a
  rw [map_zsmul, relativeFundamentalTateCup_unit_generator R S K C E p] at ha
  have he := map_zsmul (relativeTateH2Equiv R S K C E p) m (1 : ZMod d)
  have hm : (m : ZMod d) = 0 := by
    apply (relativeTateH2Equiv R S K C E p).injective
    simpa using (he.trans ha).trans (map_zero (relativeTateH2Equiv R S K C E p)).symm
  obtain ⟨j, hj⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd m d).mp hm
  rw [hj, mul_comm, mul_smul]
  have hd : (d : ℤ) • tateScalarUnit ℤ Gal(E/K) = 0 := by
    have hcard : Fintype.card Gal(E/K) = d := by
      simpa only [Nat.card_eq_fintype_card] using IsGalois.card_aut_eq_finrank K E
    rw [← hcard]
    exact tateScalarUnit_card_smul Gal(E/K)
  rw [hd]
  exact zsmul_zero (α := tateCohomology (Rep.trivial ℤ Gal(E/K) ℤ) 0) j

/-- A proved isomorphism whose forward map is the actual relative fundamental Tate cup. -/
def relativeFundamentalTateCupZeroEquiv :
    tateCohomology (Rep.trivial ℤ Gal(E/K) ℤ) 0 ≃ₗ[ℤ]
      tateCohomology (Rep.ofAlgebraAutOnUnits K E) 2 :=
  LinearEquiv.ofBijective (relativeFundamentalTateCup R S K C E 0).hom
    ⟨relativeFundamentalTateCup_zero_injective R S K C E p,
      relativeFundamentalTateCup_zero_surjective R S K C E p⟩

end LocalClassFieldTheory
