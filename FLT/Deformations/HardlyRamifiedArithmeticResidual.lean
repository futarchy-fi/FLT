/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Deformations.HardlyRamifiedTwoQuotient
public import FLT.GaloisRepresentation.HardlyRamified.CoordinateChange

/-!
# Arithmetic equations supplied by the original HR residual representation

The inertia set consists of the actual local inertia images at all primes
away from 2p. Triviality on this set is the existing unramifiedness predicate.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open GaloisRepresentation
namespace Deformation
open ProartinianCat

/-- Actual global images of all local inertia groups away from 2p. -/
def hardlyAwayInertia (p : ℕ) : Set (Field.absoluteGaloisGroup ℚ) :=
  {g | ∃ (q : ℕ) (hq : q.Prime), q ≠ 2 ∧ q ≠ p ∧
    ∃ s ∈ localInertiaGroup hq.toHeightOneSpectrumRingOfIntegersRat,
      Field.absoluteGaloisGroup.map
        (algebraMap ℚ (hq.toHeightOneSpectrumRingOfIntegersRat.adicCompletion ℚ)) s = g}

/-- The matrix equations recover the existing arithmetic unramifiedness predicate. -/
theorem trivial_hardlyAwayInertia_iff {A : Type*} [CommRing A]
    [TopologicalSpace A] [IsTopologicalRing A]
    (p : ℕ) (τ : FramedGaloisRep ℚ A (Fin 2)) :
    (∀ g ∈ hardlyAwayInertia p, FramedGaloisRep.GL τ g = 1) ↔
      ∀ q (hq : q.Prime), q ≠ 2 ∧ q ≠ p →
        τ.IsUnramifiedAt hq.toHeightOneSpectrumRingOfIntegersRat := by
  have hc (q : ℕ) (hq : q.Prime)
      (s : Field.absoluteGaloisGroup (hq.toHeightOneSpectrumRingOfIntegersRat.adicCompletion ℚ)) :
      τ.toLocal hq.toHeightOneSpectrumRingOfIntegersRat s =
        τ (Field.absoluteGaloisGroup.map
          (algebraMap ℚ (hq.toHeightOneSpectrumRingOfIntegersRat.adicCompletion ℚ)) s) := by
    exact congrArg (fun f : ℚ →+* hq.toHeightOneSpectrumRingOfIntegersRat.adicCompletion ℚ ↦
      τ (Field.absoluteGaloisGroup.map f s)) (Subsingleton.elim _ _)
  constructor
  · intro h q hq hgood
    constructor
    intro s hs
    have he := h _ ⟨q, hq, hgood.1, hgood.2, s, hs, rfl⟩
    change τ.toLocal hq.toHeightOneSpectrumRingOfIntegersRat s = 1
    rw [hc]
    apply LinearMap.toMatrix'.injective
    simpa only [FramedGaloisRep.GL_apply, LinearMap.toMatrix'_one, Units.val_one]
      using congrArg Units.val he
  · intro h g hg
    obtain ⟨q, hq, hq2, hqp, s, hs, rfl⟩ := hg
    have := h q hq ⟨hq2, hqp⟩
    have he := GaloisRep.IsUnramifiedAt.localInertiaGroup_le (ρ := τ) hs
    change τ.toLocal hq.toHeightOneSpectrumRingOfIntegersRat s = 1 at he
    rw [hc] at he
    apply Units.ext
    simpa only [FramedGaloisRep.GL_apply, LinearMap.toMatrix'_one, Units.val_one]
      using congrArg LinearMap.toMatrix' he

variable (O : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O]
  [Finite (IsLocalRing.ResidueField O)]
local notation "k" => residueField (𝓞 := O)
variable {p : ℕ} [Fact p.Prime] (hp : Odd p) [Algebra ℤ_[p] (residueField (𝓞 := O))]
  {V : Type} [AddCommGroup V] [Module (residueField (𝓞 := O)) V]
  [Module.Finite (residueField (𝓞 := O)) V] [Module.Free (residueField (𝓞 := O)) V]
  (hdim : Module.rank (residueField (𝓞 := O)) V = 2)
  (ρ : GaloisRep ℚ (residueField (𝓞 := O)) V) (hρ : IsHardlyRamified hp hdim ρ)

omit [IsNoetherianRing O] [Finite (IsLocalRing.ResidueField O)] in
/-- HR proves every residual inertia equation in the constructed frame. -/
theorem hardlyTwoFramedResidual_away :
    ∀ g ∈ hardlyAwayInertia p, hardlyTwoFramedResidual O hp hdim ρ hρ g = 1 := by
  apply (trivial_hardlyAwayInertia_iff p (ρ.conj (hardlyTwoFrame O hp hdim ρ hρ).symm)).mpr
  intro q hq hgood
  have := hρ.isUnramified q hq hgood
  infer_instance

variable [Algebra ℤ_[p] O] [IsScalarTower ℤ_[p] O (residueField (𝓞 := O))]

/-- The prescribed integral cyclotomic determinant, evaluated in the coefficient base. -/
def hardlyCyclotomicValue (g : Field.absoluteGaloisGroup ℚ) : O :=
  algebraMap ℤ_[p] O (cyclotomicCharacter (AlgebraicClosure ℚ) p g.toRingEquiv)

omit [IsNoetherianRing O] [Finite (IsLocalRing.ResidueField O)] in
/-- HR proves the residual determinant equation in the constructed frame. -/
theorem hardlyTwoFramedResidual_det (g : Field.absoluteGaloisGroup ℚ) :
    (hardlyTwoFramedResidual O hp hdim ρ hρ g : Matrix (Fin 2) (Fin 2) k).det =
      algebraMap O k (hardlyCyclotomicValue (p := p) O g) := by
  change ((ρ.conj (hardlyTwoFrame O hp hdim ρ hρ).symm) g).toMatrix'.det = _
  rw [LinearMap.det_toMatrix']
  change ((hardlyTwoFrame O hp hdim ρ hρ).symm.conj (ρ g)).det = _
  exact (LinearMap.det_conj (ρ g) (hardlyTwoFrame O hp hdim ρ hρ).symm).trans
    ((hρ.det g).trans (IsScalarTower.algebraMap_apply ℤ_[p] O k _))

end Deformation
