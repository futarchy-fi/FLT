/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.RaynaudLocalPowerExtension

/-!
# Integral transitions over the rational prime completion

The p-adic comparison proves the required ramification bound on the actual
rational completion. No transport of the prescribed point module is needed.
-/

@[expose] public noncomputable section
namespace ThreeAdicPlan
open NumberField IsLocalRing

variable (p : ℕ) [Fact p.Prime]
local notation "v" => LocalCyclotomic.rationalPlace p
local notation "O" =>
  IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ (LocalCyclotomic.rationalPlace p)
local notation "K" =>
  IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ (LocalCyclotomic.rationalPlace p)

/-- The rational place agrees with the prime place used in hardly ramifiedness. -/
theorem rationalPlace_eq_primePlace :
    v = (Fact.out : p.Prime).toHeightOneSpectrumRingOfIntegersRat := by
  ext x
  change x ∈ (Ideal.span {(p : ℤ)}).map
    (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)).symm ↔
    Rat.ringOfIntegersEquiv x ∈ Ideal.span {(p : ℤ)}
  rw [Ideal.map_symm]
  change Rat.IsIntegralClosure.intEquiv (𝓞 ℚ) x ∈ Ideal.span {(p : ℤ)} ↔
    Rat.ringOfIntegersEquiv x ∈ Ideal.span {(p : ℤ)}
  rw [Rat.IsIntegralClosure.intEquiv_apply_eq_ringOfIntegersEquiv]

/-- Every prescribed map extends uniquely over the original rational completion. -/
theorem extend_from_rational_power {X Y : FF O K} (hp : 2 < p)
    (hX : KilledByPowerOf p X) (f : GenericGaloisHom X Y) :
    ∃! g : ModelHom X Y, genericHom g = f := by
  let : IsAdicComplete (maximalIdeal O) O := rationalCompletionIntegers_adicComplete p
  let : CharP (ResidueField O) p := (LocalCyclotomic.residueEquiv p).toRingHom.charP
    (LocalCyclotomic.residueEquiv p).injective p
  let e : ℤ_[p] ≃+* O :=
    (PadicInt.adicCompletionIntegersEquiv (𝓞 ℚ) ⟨p, Fact.out⟩).toAlgEquiv.toRingEquiv
  have hπ : Irreducible (p : O) := by
    simpa only [map_natCast] using (MulEquiv.irreducible_iff (f := e)).mpr PadicInt.irreducible_p
  apply extend_from_local_power v p _ hX f
  rw [RaynaudParameters.order, IsDiscreteValuationRing.addVal_uniformizer hπ]
  simp only [ENat.toNat_one]
  omega

/-- The chosen integral map retains the prescribed generic point map. -/
def GenericGaloisHom.rationalExtension {X Y : FF O K} (f : GenericGaloisHom X Y)
    (hp : 2 < p) (hX : KilledByPowerOf p X) : ModelHom X Y :=
  (extend_from_rational_power p hp hX f).exists.choose

/-- Generic restriction of the rational-completion extension is exact. -/
@[simp] theorem GenericGaloisHom.genericHom_rationalExtension {X Y : FF O K}
    (f : GenericGaloisHom X Y)
    (hp : 2 < p) (hX : KilledByPowerOf p X) :
    genericHom (f.rationalExtension p hp hX) = f :=
  (extend_from_rational_power p hp hX f).exists.choose_spec

/-- Integral extension preserves composition of the actual generic maps. -/
theorem GenericGaloisHom.rationalExtension_comp {X Y Z : FF O K}
    (f : GenericGaloisHom X Y) (g : GenericGaloisHom Y Z)
    (hp : 2 < p) (hX : KilledByPowerOf p X) (hY : KilledByPowerOf p Y) :
    GenericGaloisHom.rationalExtension p (g.comp f) hp hX =
      (f.rationalExtension p hp hX).comp (g.rationalExtension p hp hY) := by
  apply genericHom_injective
  ext x
  simp only [genericHom_rationalExtension, genericHom_comp, DistribMulActionHom.comp_apply]

end ThreeAdicPlan
