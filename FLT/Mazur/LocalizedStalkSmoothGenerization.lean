/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.RingTheory.Etale.Locus
public import Mathlib.RingTheory.Localization.LocalizationLocalization

/-!
# Smooth generizations detected by a punctured local ring

If a local ring at p becomes formally smooth after inverting t, every
prime below p that avoids t is smooth in the original affine algebra.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.LocalizedStalkSmoothGenerization

set_option backward.isDefEq.respectTransparency false

variable (R A L B : Type*) [CommRing R] [CommRing A] [CommRing L] [CommRing B]
  [Algebra R A] [Algebra A L] [Algebra R L] [IsScalarTower R A L]
  [Algebra L B] [Algebra R B] [IsScalarTower R L B]
  (p : Ideal A) [p.IsPrime] [IsLocalization.AtPrime L p]
  (t : A) [IsLocalization.Away (algebraMap A L t) B]
  [Algebra.FormallySmooth R B]

include L B p t in
/-- Punctured-stalk formal smoothness proves smoothness at every prime below p avoiding t. -/
theorem isSmoothAt (q : Ideal A) [q.IsPrime] (hqp : q ≤ p) (ht : t ∉ q) :
    Algebra.IsSmoothAt R q := by
  let S := Localization.AtPrime q
  have hle : p.primeCompl ≤ q.primeCompl := fun _ ha hq ↦ ha (hqp hq)
  let _ : Algebra L S := IsLocalization.localizationAlgebraOfSubmonoidLe
    L S p.primeCompl q.primeCompl hle
  let _ : IsScalarTower A L S :=
    IsLocalization.localization_isScalarTower_of_submonoid_le L S
      p.primeCompl q.primeCompl hle
  let _ : IsScalarTower R L S := IsScalarTower.to₁₃₄ R A L S
  let N := q.primeCompl.map (algebraMap A L)
  let _ : IsLocalization N S :=
    IsLocalization.isLocalization_of_submonoid_le L S p.primeCompl q.primeCompl hle
  have htN : Submonoid.powers (algebraMap A L t) ≤ N :=
    Submonoid.powers_le.mpr ⟨t, ht, rfl⟩
  let _ : Algebra B S := IsLocalization.localizationAlgebraOfSubmonoidLe
    B S (Submonoid.powers (algebraMap A L t)) N htN
  let _ : IsScalarTower L B S :=
    IsLocalization.localization_isScalarTower_of_submonoid_le B S
      (Submonoid.powers (algebraMap A L t)) N htN
  let _ : IsScalarTower R B S := IsScalarTower.to₁₃₄ R L B S
  let _ : IsLocalization (N.map (algebraMap L B)) S :=
    IsLocalization.isLocalization_of_submonoid_le B S
      (Submonoid.powers (algebraMap A L t)) N htN
  let _ : Algebra.FormallySmooth B S :=
    Algebra.FormallySmooth.of_isLocalization (N.map (algebraMap L B))
  exact Algebra.FormallySmooth.comp R B S

end FLT.Mazur.LocalizedStalkSmoothGenerization
