/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial

/-!
# Actual affine etale lifts across nilpotent closed immersions

Formal smoothness supplies a lift of the ring homomorphism of global sections.
Affine anti-equivalence turns it into a whole scheme morphism, and formal
unramifiedness proves uniqueness. No pointwise or reduced replacement occurs.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Opposite
namespace FLT.Mazur.AffineEtaleNilpotentLift
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {T Y : Scheme} [IsAffine T] [IsAffine Y]

/-- Recover a whole affine scheme morphism from its regular-function homomorphism. -/
def ofSections (φ : Γ(Y, ⊤) ⟶ Γ(T, ⊤)) : T ⟶ Y :=
  (AffineScheme.Γ.preimage (X := op (AffineScheme.of Y))
    (Y := op (AffineScheme.of T)) φ).unop.hom

/-- The recovered scheme map has exactly the supplied regular-function map. -/
theorem ofSections_appTop (φ : Γ(Y, ⊤) ⟶ Γ(T, ⊤)) : (ofSections φ).appTop = φ :=
  AffineScheme.Γ.map_preimage (X := op (AffineScheme.of Y))
    (Y := op (AffineScheme.of T)) φ

/-- Global sections distinguish whole affine scheme maps. -/
theorem hom_ext {a b : T ⟶ Y} (h : a.appTop = b.appTop) : a = b := by
  have he : (AffineScheme.ofHom a).op = (AffineScheme.ofHom b).op :=
    AffineScheme.Γ.map_injective h
  exact congrArg (fun v : op (AffineScheme.of Y) ⟶ op (AffineScheme.of T) ↦ v.unop.hom) he

variable {T₀ Z : Scheme} [IsAffine T₀] [IsAffine Z]
  (i : T₀ ⟶ T) [IsClosedImmersion i] (hi : IsNilpotent i.ker)
  (g : Y ⟶ Z) [Etale g] (a : T₀ ⟶ Y) (v : T ⟶ Z) (ha : i ≫ v = a ≫ g)

include hi ha in
/-- An affine etale square over a nilpotent closed immersion has a unique whole scheme lift. -/
theorem existsUnique_lift : ∃! b : T ⟶ Y, i ≫ b = a ∧ b ≫ g = v := by
  have hg : g.appTop.hom.Etale :=
    (HasRingHomProperty.iff_of_isAffine (P := @Etale) (f := g)).mp inferInstance
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
  refine ⟨b, ⟨hba, hbg⟩, ?_⟩
  intro b' hb'
  exact FormallyUnramified.hom_ext i hi g (hb'.1.trans hba.symm) (hb'.2.trans hbg.symm)

end FLT.Mazur.AffineEtaleNilpotentLift
