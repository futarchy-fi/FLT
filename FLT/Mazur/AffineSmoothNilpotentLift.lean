/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineEtaleNilpotentLift
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-!
# Whole affine smooth lifts across nilpotent immersions

Formal smoothness lifts the original map of global sections. Affine
anti-equivalence recovers an actual scheme map with the prescribed reduction
and structure map. Neither coefficient ring is required to be local.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.AffineSmoothNilpotentLift

open AffineEtaleNilpotentLift

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {T₀ T Y Z : Scheme} [IsAffine T₀] [IsAffine T] [IsAffine Y] [IsAffine Z]
  (i : T₀ ⟶ T) [IsClosedImmersion i] (hi : IsNilpotent i.ker)
  (g : Y ⟶ Z) [Smooth g] (a : T₀ ⟶ Y) (v : T ⟶ Z) (ha : i ≫ v = a ≫ g)

include hi ha in
/-- A smooth affine target admits a whole lift over every affine nilpotent thickening. -/
theorem exists_lift : ∃ b : T ⟶ Y, i ≫ b = a ∧ b ≫ g = v := by
  have hg : g.appTop.hom.Smooth :=
    (HasRingHomProperty.iff_of_isAffine (P := @Smooth) (f := g)).mp inferInstance
  algebraize [g.appTop.hom, v.appTop.hom, (i ≫ v).appTop.hom]
  let α : Γ(Y, ⊤) →ₐ[Γ(Z, ⊤)] Γ(T₀, ⊤) :=
    ⟨a.appTop.hom, fun r ↦ congrArg (fun w : T₀ ⟶ Z ↦ w.appTop r) ha.symm⟩
  let ρ : Γ(T, ⊤) →ₐ[Γ(Z, ⊤)] Γ(T₀, ⊤) := ⟨i.appTop.hom, fun _ ↦ rfl⟩
  have hρ : Function.Surjective ρ :=
    (IsClosedImmersion.isAffine_surjective_of_isAffine i).2
  have hn : IsNilpotent (RingHom.ker ρ.toRingHom) := by
    obtain ⟨n, hn⟩ := hi
    change i.ker ^ n = ⊥ at hn
    refine ⟨n, ?_⟩
    have he := congrArg (fun J : T.IdealSheafData ↦ J.ideal ⟨⊤, isAffineOpen_top T⟩) hn
    simpa only [Scheme.IdealSheafData.ideal_pow, Pi.pow_apply, Scheme.Hom.ker_apply,
      Scheme.IdealSheafData.ideal_bot, Pi.bot_apply, Ideal.zero_eq_bot, ρ,
      Scheme.Hom.appTop] using he
  let φ := Algebra.FormallySmooth.liftOfSurjective α ρ hρ hn
  let b := ofSections (CommRingCat.ofHom φ.toRingHom)
  have hb : b.appTop = CommRingCat.ofHom φ.toRingHom := ofSections_appTop _
  have hba : i ≫ b = a := by
    apply hom_ext
    rw [Scheme.Hom.comp_appTop, hb]
    apply CommRingCat.hom_ext
    exact congrArg AlgHom.toRingHom (Algebra.FormallySmooth.comp_liftOfSurjective α ρ hρ hn)
  have hbg : b ≫ g = v := by
    apply hom_ext
    rw [Scheme.Hom.comp_appTop, hb]
    apply CommRingCat.hom_ext
    apply RingHom.ext
    exact φ.commutes
  exact ⟨b, hba, hbg⟩

end FLT.Mazur.AffineSmoothNilpotentLift
