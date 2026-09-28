/-
Copyright (c) 2026 FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FLT Project
-/
module

public import FLT.GaloisRepresentation.HardlyRamified.CategoryDSimple
public import FLT.RepresentationTheory.SmallQuotient
public import Mathlib.Algebra.Module.ZMod

/-!
# Simple category-D objects and prime-field representations

Simplicity of the finite-flat object gives irreducibility over the prime field
by applying the definition to the underlying additive subgroup of each
subrepresentation. This does not assume that restriction of scalars preserves
irreducibility. The arithmetic input identifying the finite Galois quotient is
kept explicit in the conditional point-classification theorem.
-/

@[expose] public noncomputable section

namespace ThreeAdicPlan

local notation "Γ" => AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ

/-- The canonical prime-field module structure of a simple category-D object. -/
abbrev Simple.threeModule {H : FiniteFlatObject ZInvTwo} (hs : Simple H)
    (hD : InCategoryD H) : Module (ZMod 3) H.points :=
  AddCommGroup.zmodModule (simple_D_killed_three H hs hD)

/-- The rational Galois action on a point group killed by three, as a
representation over the prime field. -/
def FiniteFlatObject.threeRepresentation {R : Type} [CommRing R] [Algebra R ℚ]
    (H : FiniteFlatObject R) [Module (ZMod 3) H.points] :
    Representation (ZMod 3) Γ H.points where
  toFun σ := (DistribMulAction.toAddMonoidEnd Γ H.points σ).toZModLinearMap 3
  map_one' := by ext; exact one_smul _ _
  map_mul' := by intros; ext; exact mul_smul _ _ _

/-- Simplicity of a finite-flat object implies prime-field irreducibility for
any representation through which its full Galois action factors. -/
theorem Simple.isIrreducible_of_pointAction {R : Type} [CommRing R] [Algebra R ℚ]
    {H : FiniteFlatObject R} (hs : Simple H) [Module (ZMod 3) H.points]
    {G : Type*} [Group G] (ρ : Representation (ZMod 3) G H.points)
    (φ : Γ →* G) (hρ : ∀ σ w, ρ (φ σ) w = σ • w) :
    Representation.IsIrreducible ρ := by
  have : Nontrivial H.points := hs.1
  refine { exists_pair_ne := ?_, eq_bot_or_eq_top := ?_ }
  · refine ⟨⊥, ⊤, ?_⟩
    intro h
    obtain ⟨w, hw⟩ := exists_ne (0 : H.points)
    have hmem : w ∈ (⊥ : Subrepresentation ρ) := by rw [h]; trivial
    exact hw hmem
  · intro S
    have hstable : GaloisStable H.points S.toSubmodule.toAddSubgroup := by
      intro σ w hw
      rw [← hρ σ w]
      exact S.apply_mem_toSubmodule (φ σ) hw
    rcases hs.2 S.toSubmodule.toAddSubgroup hstable with h | h
    · left
      apply SetLike.coe_injective
      exact congrArg (fun A : AddSubgroup H.points ↦ (A : Set H.points)) h
    · right
      apply SetLike.coe_injective
      exact congrArg (fun A : AddSubgroup H.points ↦ (A : Set H.points)) h

/-- In particular, the full rational Galois representation is irreducible
over the prime field. -/
theorem Simple.threeRepresentation_isIrreducible {R : Type} [CommRing R] [Algebra R ℚ]
    {H : FiniteFlatObject R} (hs : Simple H) [Module (ZMod 3) H.points] :
    Representation.IsIrreducible H.threeRepresentation :=
  hs.isIrreducible_of_pointAction H.threeRepresentation (MonoidHom.id Γ) (fun _ _ ↦ rfl)

/-- Conditional classification of the points of a simple object, once the
arithmetic argument supplies a quotient with a normal 3-subgroup and residual
order dividing two. This asserts no identification of integral models. -/
theorem Simple.points_three_of_normal_threeSubgroup {H : FiniteFlatObject ZInvTwo}
    (hs : Simple H) [Module (ZMod 3) H.points]
    {G : Type*} [Group G] (ρ : Representation (ZMod 3) G H.points)
    (φ : Γ →* G) (hρ : ∀ σ w, ρ (φ σ) w = σ • w)
    (P : Subgroup G) [P.Normal] [Finite P] (hP : IsPGroup 3 P)
    (hcard : Nat.card (G ⧸ P) ∣ 2) :
    Module.finrank (ZMod 3) H.points = 1 ∧
      ∃ χ : Γ →* (ZMod 3)ˣ,
        (∀ σ, χ σ = 1 ∨ χ σ = -1) ∧
        (∀ (σ : Γ) (w : H.points), σ • w = (χ σ : ZMod 3) • w) := by
  let := hs.isIrreducible_of_pointAction ρ φ hρ
  obtain ⟨hdim, χ, hsign, hχ⟩ := ρ.simple_three_of_normal_threeSubgroup P hP hcard
  exact ⟨hdim, χ.comp φ, fun σ ↦ hsign (φ σ), fun σ w ↦ (hρ σ w).symm.trans (hχ _ _)⟩

end ThreeAdicPlan
