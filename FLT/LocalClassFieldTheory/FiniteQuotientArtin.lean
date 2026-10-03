/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.AbelianizationQuotientExact
public import FLT.LocalClassFieldTheory.FiniteArtinNormImage
public import FLT.LocalClassFieldTheory.FiniteTateNormTower

/-!
# The actual quotient Artin map and its norm kernel

Projecting the constructed Artin map to the quotient Galois group's
abelianization is surjective. Its kernel is exactly the fixed-field norm.
Equality with the independently constructed lower-field Artin map still
requires the fundamental cup's deflation diagram.
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
  (F : IntermediateField K C) [IsGalois K F] [FiniteDimensional K F]
  [Algebra S F] [IsFractionRing S F] [Algebra S C] [IsScalarTower S F C]
  [IsScalarTower R S F] [IsScalarTower R S C]
  [Algebra.IsSeparable K C] [IsSepClosed C]
  [Finite (ResidueField R)] [Finite (ResidueField S)]
  [IsAdicComplete (maximalIdeal R) R] [IsAdicComplete (maximalIdeal S) S]

attribute [local instance] relativeBaseTower unramifiedUnionGalois fieldUnitAction
  unramifiedFieldUnitTopology unramifiedFieldUnitDiscrete
  separableClosureGalois separableClosureUnitTopology separableClosureUnitDiscrete

variable [TopologicalSpace (Additive Fˣ)] [DiscreteTopology (Additive Fˣ)]
  [CharZero C] (p : ℕ) [Fact p.Prime]
  [CharP (ResidueField R) p] [CharP (ResidueField S) p]

local notation "M" => Rep.ofAlgebraAutOnUnits K F

variable (H : Subgroup Gal(F/K))

local notation "MH" => Rep.res H.subtype M


local notation "E" => IntermediateField.fixedField H

variable [H.Normal]

/-- The actual quotient of the finite Artin map. -/
def finiteQuotientArtin : Additive Kˣ →+ Additive (Abelianization (Gal(F/K) ⧸ H)) :=
  (Abelianization.map (QuotientGroup.mk' H)).toAdditive.comp (finiteArtin R S K C F p)

/-- The actual quotient Artin map is surjective. -/
theorem finiteQuotientArtin_surjective :
    Function.Surjective (finiteQuotientArtin R S K C F p H) :=
  (abelianization_quotient_surjective H).comp (finiteArtin_surjective R S K C F p)

/-- The kernel of the actual quotient Artin map is the fixed-field algebraic norm. -/
theorem finiteQuotientArtin_eq_zero_iff (u : Additive Kˣ) :
    finiteQuotientArtin R S K C F p H u = 0 ↔
      ∃ v : Eˣ, Units.map (Algebra.norm K) v = u.toMul := by
  classical
  let : Fintype H := Fintype.ofFinite _
  constructor
  · intro h
    change Abelianization.map (QuotientGroup.mk' H)
      (Additive.toMul (finiteArtin R S K C F p u)) = 1 at h
    obtain ⟨b, hb⟩ := (abelianization_quotient_eq_one_iff H _).mp h
    have hi : ∃ b : Additive (Abelianization H),
        (Abelianization.map H.subtype).toAdditive b = finiteArtin R S K C F p u :=
      ⟨Additive.ofMul b, hb⟩
    obtain ⟨v, hv⟩ := (finiteArtin_fixedField_norm_image R S K C F p H _).mpr hi
    let n : Additive Kˣ := Additive.ofMul (Units.map (Algebra.norm K) v)
    have hn : finiteArtin R S K C F p n = finiteArtin R S K C F p u := hv
    have hz : finiteArtin R S K C F p (u - n) = 0 := by
      rw [map_sub, hn, sub_self]
    obtain ⟨w, hw⟩ := (finiteArtin_eq_zero_iff R S K C F p (u - n)).mp hz
    refine ⟨v * Units.map (Algebra.norm E) w, ?_⟩
    rw [map_mul, unitNorm_tower K E F, hw]
    apply Additive.ofMul.injective
    change n + (u - n) = u
    abel
  · rintro ⟨v, hv⟩
    have hu : u = Additive.ofMul (Units.map (Algebra.norm K) v) :=
      Additive.toMul.injective hv.symm
    change (Abelianization.map (QuotientGroup.mk' H)).toAdditive
      (finiteArtin R S K C F p u) = 0
    rw [hu, finiteArtin_arbitraryFixedField_norm]
    change Abelianization.map (QuotientGroup.mk' H)
      (Abelianization.map H.subtype _) = 1
    exact (abelianization_quotient_eq_one_iff H _).mpr ⟨_, rfl⟩

end LocalClassFieldTheory
