/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SectionGradedPullbackRing
public import FLT.Mazur.SectionGradedBaseChange

/-!
# Multiplication under flat section base change

The existing degreewise base-change isomorphisms preserve multiplication
on scalar tensors of arbitrary sections, in every pair of degrees.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
open scoped ChangeOfRings
namespace FLT.Mazur.LinePowerSectionBaseChange
open FCurve ModuleLineBundleTensorPullback SectionGradedMultiplication
open OpenModuleSectionScalars SectionGradedPullback
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {P X T S : Scheme} [CompactSpace X] [X.IsSeparated] [IsAffine T] [IsAffine S]
  {p : P ⟶ X} {q : P ⟶ T} {f : X ⟶ S} {g : T ⟶ S} [Flat g]
  (h : IsPullback p q f g) (L : X.Modules) (hL : LocallyFreeRankOne L)

/-- Flat base change preserves the product of scalar tensors of arbitrary sections. -/
lemma degreeIso_tmul_mul (m n : ℕ) (b c : Γ(T, ⊤))
    (s : Piece L ⊤ m) (t : Piece L ⊤ n) :
    (degreeIso h L hL (m + n)).hom
      ((b * c) ⊗ₜ[Γ(S, ⊤),g.appTop.hom] mul L ⊤ m n s t) =
      mul ((pullback p).obj L) ⊤ m n
        ((degreeIso h L hL m).hom (b ⊗ₜ[Γ(S, ⊤),g.appTop.hom] s))
        ((degreeIso h L hL n).hom (c ⊗ₜ[Γ(S, ⊤),g.appTop.hom] t)) := by
  rw [degreeIso_tmul, degreeIso_tmul, degreeIso_tmul]
  let ρ : Γ(T, ⊤) →+* Γ(P, ⊤) :=
    (P.presheaf.map (homOfLE (le_top : (⊤ : P.Opens) ≤ ⊤)).op).hom.comp q.appTop.hom
  change (ρ (b * c)) • ((tensorPowerIso p L (m + n)).hom.app ⊤
      (pullGlobal p _ (mul L ⊤ m n s t))) =
    mul ((pullback p).obj L) ⊤ m n
      ((ρ b) • (tensorPowerIso p L m).hom.app ⊤ (pullGlobal p _ s))
      ((ρ c) • (tensorPowerIso p L n).hom.app ⊤ (pullGlobal p _ t))
  rw [smul_mul_smul, map_mul]
  congr 1
  exact pull_mul p L m n ⊤ s t

/-- The degree-zero comparison sends the scalar tensor of units to the unit section. -/
lemma degreeIso_tmul_one :
    (degreeIso h L hL 0).hom
      ((1 : Γ(T, ⊤)) ⊗ₜ[Γ(S, ⊤),g.appTop.hom] (1 : Γ(X, ⊤))) = (1 : Γ(P, ⊤)) := by
  rw [degreeIso_tmul, one_smul]
  exact (pull_zero p L ⊤ (1 : Γ(X, ⊤))).trans (map_one p.appTop.hom)

end FLT.Mazur.LinePowerSectionBaseChange
