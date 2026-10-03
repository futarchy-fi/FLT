/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.CyclicPeriodicHomology
public import Mathlib.Data.ZMod.Basic

/-!
# Cyclic cohomology of the trivial integer module

The difference operator is zero and the norm is multiplication by the group
order. The even quotient is Z/n and the odd quotient vanishes.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace LocalClassFieldTheory

open CategoryTheory Limits Rep.FiniteCyclicGroup

variable (G : Type) [CommGroup G] [Fintype G] (g : G)
  (hg : ∀ x, x ∈ Subgroup.zpowers g)

/-- On trivial integer coefficients, norm is multiplication by the group order. -/
theorem trivialInteger_norm (x : ℤ) :
    (Rep.trivial ℤ G ℤ).norm.hom x = (Fintype.card G : ℤ) * x := by
  rw [Rep.norm_apply]
  simp [Representation.norm]

/-- Every integer is a cycle in positive even degree. -/
def trivialIntegerCycles : ℤ ≃ₗ[ℤ]
    LinearMap.ker (Rep.applyAsHom (Rep.trivial ℤ G ℤ) g - 𝟙 _).hom.toLinearMap :=
  LinearEquiv.ofBijective
    ((LinearMap.id : ℤ →ₗ[ℤ] ℤ).codRestrict _ (fun x => by change x - x = 0; exact sub_self x))
    ⟨fun _ _ h => congrArg Subtype.val h, fun x => ⟨x.val, by ext; rfl⟩⟩

/-- The quotient map from integers to positive even cohomology. -/
def trivialIntegerH2Projection : ℤ →ₗ[ℤ] groupCohomology (Rep.trivial ℤ G ℤ) 2 :=
  (groupCohomologyπEven (Rep.trivial ℤ G ℤ) g hg 2 (by decide)).hom.comp
    (trivialIntegerCycles G g).toLinearMap

/-- The integer cycle projection is surjective. -/
theorem trivialIntegerH2Projection_surjective :
    Function.Surjective (trivialIntegerH2Projection G g hg) := by
  intro x
  obtain ⟨y, hy⟩ := (ModuleCat.epi_iff_surjective
    (groupCohomologyπEven (Rep.trivial ℤ G ℤ) g hg 2 (by decide))).1 inferInstance x
  refine ⟨(trivialIntegerCycles G g).symm y, ?_⟩
  change (groupCohomologyπEven (Rep.trivial ℤ G ℤ) g hg 2 (by decide)).hom
    ((trivialIntegerCycles G g) ((trivialIntegerCycles G g).symm y)) = x
  rw [LinearEquiv.apply_symm_apply]
  exact hy

/-- The projection kills exactly the multiples of the group order. -/
theorem trivialIntegerH2Projection_eq_zero (x : ℤ) :
    trivialIntegerH2Projection G g hg x = 0 ↔ (Fintype.card G : ℤ) ∣ x := by
  rw [trivialIntegerH2Projection, LinearMap.comp_apply,
    groupCohomologyπEven_eq_zero_iff]
  change (∃ y : ℤ, (Rep.trivial ℤ G ℤ).norm.hom y = x) ↔ _
  constructor
  · rintro ⟨y, hy⟩
    exact ⟨y, hy.symm.trans (trivialInteger_norm G y)⟩
  · rintro ⟨y, hy⟩
    exact ⟨y, (trivialInteger_norm G y).trans hy.symm⟩

/-- The actual second cohomology is linearly equivalent to Z/n. -/
def trivialIntegerH2Equiv :
    groupCohomology (Rep.trivial ℤ G ℤ) 2 ≃ₗ[ℤ] ZMod (Fintype.card G) := by
  let f := trivialIntegerH2Projection G g hg
  let q := (Int.castAddHom (ZMod (Fintype.card G))).toIntLinearMap
  have hker : f.ker = q.ker := by
    ext x
    exact (trivialIntegerH2Projection_eq_zero G g hg x).trans
      (ZMod.intCast_zmod_eq_zero_iff_dvd x (Fintype.card G)).symm
  exact (f.quotKerEquivOfSurjective (trivialIntegerH2Projection_surjective G g hg)).symm.trans
    ((Submodule.quotEquivOfEq _ _ hker).trans
      (q.quotKerEquivOfSurjective ZMod.intCast_surjective))

include hg in
/-- The order of trivial integer H² is the group order. -/
theorem trivialInteger_H2_card :
    Nat.card (groupCohomology (Rep.trivial ℤ G ℤ) 2) = Fintype.card G := by
  rw [Nat.card_congr (trivialIntegerH2Equiv G g hg).toEquiv, Nat.card_zmod]

omit [Fintype G] in
include hg in
/-- Trivial integer H¹ vanishes because the norm is injective. -/
theorem trivialInteger_H1_isZero [Finite G] : IsZero (groupCohomology (Rep.trivial ℤ G ℤ) 1) := by
  let := Fintype.ofFinite G
  apply IsZero.of_iso _ (groupCohomologyIsoOdd (Rep.trivial ℤ G ℤ) g hg 1 (by decide))
  apply (ShortComplex.exact_iff_isZero_homology _).mp
  rw [ShortComplex.moduleCat_exact_iff]
  intro x hx
  have h : (Fintype.card G : ℤ) * x = 0 := (trivialInteger_norm G x).symm.trans hx
  have hx0 : x = 0 := (mul_eq_zero.mp h).resolve_left
    (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
  exact ⟨0, by simp [hx0]⟩

omit [Fintype G] in
include hg in
/-- Trivial integer H¹ has one element. -/
theorem trivialInteger_H1_card [Finite G] :
    Nat.card (groupCohomology (Rep.trivial ℤ G ℤ) 1) = 1 := by
  have := ModuleCat.isZero_iff_subsingleton.mp (trivialInteger_H1_isZero G g hg)
  simp

end LocalClassFieldTheory
