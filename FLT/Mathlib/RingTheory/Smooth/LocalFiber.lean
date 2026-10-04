/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.RingTheory.Smooth.Fiber

/-!
# Smoothness detected on the fibre of a local algebra

This is the prime-local version of the fibre criterion, Stacks 00TF.
Unlike `Algebra.IsSmoothAt.of_formallySmooth_fiber`, only the fibre of
`S_q`, rather than the whole fibre of `S`, has to be formally smooth.
-/

public noncomputable section

open TensorProduct

namespace Algebra

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- A flat finitely presented algebra is smooth at `q` when the fibre of
its localization at `q` is formally smooth. -/
theorem IsSmoothAt.of_formallySmooth_localFiber [Module.Flat R S]
    [FinitePresentation R S] (p : Ideal R) (q : Ideal S)
    [p.IsPrime] [q.IsPrime] [q.LiesOver p]
    [FormallySmooth p.ResidueField (p.Fiber (Localization.AtPrime q))] :
    IsSmoothAt R q := by
  let Rp := Localization.AtPrime p
  let Sp := Localization (algebraMapSubmonoid S p.primeCompl)
  let Sq := Localization.AtPrime q
  let := Localization.AtPrime.algebraOfLiesOver p q
  let f : Sp →ₐ[S] Sq := IsLocalization.liftAlgHom
    (M := algebraMapSubmonoid S p.primeCompl) (f := Algebra.ofId _ _) (by
      rintro ⟨_, x, hx, rfl⟩
      simpa only [Algebra.ofId_apply, ← IsScalarTower.algebraMap_apply R S Sq] using
        IsLocalization.map_units (M := q.primeCompl) Sq
        ⟨algebraMap _ _ x, by simp_all [q.over_def p]⟩)
  algebraize [f.toRingHom]
  have : IsScalarTower R Sp Sq := .to₁₃₄ _ S _ _
  have : IsScalarTower Rp Sp Sq := .of_algebraMap_eq' <| by
    apply IsLocalization.ringHom_ext p.primeCompl
    simp only [RingHom.comp_assoc, ← IsScalarTower.algebraMap_eq]
  have : IsLocalization (algebraMapSubmonoid Sp q.primeCompl) Sq :=
    .isLocalization_of_submonoid_le _ _ (algebraMapSubmonoid S p.primeCompl) _
      (by rintro _ ⟨x, hx, rfl⟩; simp_all [q.over_def p])
  have : FinitePresentation Rp Sp := by
    have : IsPushout R Rp S Sp :=
      .symm <| Algebra.isPushout_of_isLocalization p.primeCompl _ _ _
    exact .equiv (IsPushout.equiv R Rp S Sp)
  have : FormallySmooth (IsLocalRing.ResidueField Rp)
      (IsLocalRing.ResidueField Rp ⊗[Rp] Sq) :=
    .of_equiv (TensorProduct.equivOfCompatibleSMul Rp R p.ResidueField p.ResidueField Sq)
  have := FormallySmooth.of_formallySmooth_residueField_tensor
    (R := Rp) (S := Sq) (P := Sp) (algebraMapSubmonoid _ q.primeCompl)
  exact .comp R Rp Sq

/-- Smoothness at a prime is equivalent to smoothness of the fibre of the
localized algebra, for a flat finitely presented algebra. -/
theorem isSmoothAt_iff_formallySmooth_localFiber [Module.Flat R S]
    [FinitePresentation R S] (p : Ideal R) (q : Ideal S)
    [p.IsPrime] [q.IsPrime] [q.LiesOver p] :
    IsSmoothAt R q ↔ FormallySmooth p.ResidueField (p.Fiber (Localization.AtPrime q)) := by
  constructor
  · intro h
    infer_instance
  · intro h
    exact .of_formallySmooth_localFiber p q

end Algebra
