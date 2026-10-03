/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.OneCocycleInvariantProjection

/-!
# The divided invariant extension is short exact

Taking subgroup invariants of the twisted extension and dividing its scalar
projection by the subgroup order produces a quotient-group short exact
sequence. The kernel and the surjection are proved on the concrete modules.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace LocalClassFieldTheory

open CategoryTheory groupCohomology

variable {G : Type} [Group G] (Q : Rep.{0} ℤ G) (b : cocycles₁ Q)
  (N : Subgroup G) [N.Normal] [Fintype N]
  (h₀ : Limits.IsZero (tateCohomology (Rep.res N.subtype (oneCocycleExtension Q b)) 0))

local notation "X" => oneCocycleExtension Q b
local notation "XQ" => Rep.quotientToInvariants X N
local notation "QQ" => Rep.quotientToInvariants Q N
local notation "i" =>
  CategoryTheory.Functor.map (Rep.quotientToInvariantsFunctor ℤ N) (oneCocycleInclusion Q b)
local notation "π" => oneCocycleInvariantProjection Q b N h₀

/-- Retain the original integral module structure for invariant inclusion. -/
local instance oneCocycleInvariantBaseModule : Module ℤ Q := Q.hV2

/-- Retain the twisted extension's integral module structure for inflation. -/
local instance oneCocycleInvariantExtensionModule : Module ℤ (oneCocycleExtension Q b) :=
  (oneCocycleExtension Q b).hV2

/-- The quotient-group extension uses the divided scalar projection. -/
def oneCocycleInvariantSequence : ShortComplex (Rep ℤ (G ⧸ N)) :=
  ShortComplex.mk i π (by ext x; change (0 : ℤ) / (Fintype.card N : ℤ) = 0; simp)

/-- A zero divided scalar coordinate is exactly the image of an invariant coefficient. -/
theorem oneCocycleInvariantSequence_kernel (x : XQ) (hx : (π).hom x = 0) :
    ∃ y : QQ, (i).hom y = x := by
  have hs : x.val.2 = 0 := by
    have h := oneCocycleInvariantProjection_mul Q b N h₀ x
    rw [hx, zero_mul] at h
    exact h.symm
  refine ⟨⟨x.val.1, fun n => ?_⟩, ?_⟩
  · have hinj : Function.Injective (oneCocycleInclusion Q b).hom :=
      fun _ _ h => congrArg Prod.fst h
    apply hinj
    have he : (oneCocycleInclusion Q b).hom x.val.1 = x.val := Prod.ext rfl hs.symm
    exact (Rep.hom_comm_apply (oneCocycleInclusion Q b) (n : G) x.val.1).trans
      ((congrArg ((X).ρ (n : G)) he).trans ((x.property n).trans he.symm))
  · apply Subtype.ext
    exact Prod.ext rfl hs.symm

/-- The divided invariant extension is genuinely short exact. -/
theorem oneCocycleInvariantSequence_shortExact :
    (oneCocycleInvariantSequence Q b N h₀).ShortExact where
  mono_f := (Rep.mono_iff_injective _).mpr (by
    intro x y h
    apply Subtype.ext
    exact congrArg (fun z : XQ => z.val.1) h)
  epi_g := (Rep.epi_iff_surjective _).mpr
    (oneCocycleInvariantProjection_surjective Q b N h₀)
  exact := by
    rw [← ShortComplex.exact_map_iff_of_faithful _ (forget₂ (Rep ℤ (G ⧸ N)) (ModuleCat ℤ))]
    exact (ShortComplex.moduleCat_exact_iff _).mpr
      (oneCocycleInvariantSequence_kernel Q b N h₀)

/-- Inflation of the divided extension maps to the original extension with scalar factor |N|. -/
def oneCocycleInvariantSequenceMap :
    (oneCocycleInvariantSequence Q b N h₀).map (Rep.resFunctor (QuotientGroup.mk' N)) ⟶
      oneCocycleSequence Q b where
  τ₁ := ConcreteCategory.ofHom (C := Rep ℤ G) (Q.ρ.quotientToInvariants_lift N)
  τ₂ := ConcreteCategory.ofHom (C := Rep ℤ G) ((X).ρ.quotientToInvariants_lift N)
  τ₃ := (Fintype.card N : ℤ) • 𝟙 _
  comm₁₂ := by ext x; rfl
  comm₂₃ := by
    ext x
    change x.val.2 = (Fintype.card N : ℤ) * (π).hom x
    rw [mul_comm]
    exact (oneCocycleInvariantProjection_mul Q b N h₀ x).symm

end LocalClassFieldTheory
