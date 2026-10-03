/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.RaynaudHenselianScalarRigidity
public import FLT.GroupScheme.RaynaudDescentScalarFiltration
public import FLT.AbsoluteGaloisGroup.InertiaDescentHenselian

/-!
# Integral rigidity over a local number-field completion

The finite unramified inertia descent constructs the scalar filtration.
Henselian rigidity and faithful flatness bring surjectivity back to the
original integral models. No filtration or scalar-field data are inputs.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace ThreeAdicPlan
open NumberField IsLocalRing IsDiscreteValuationRing

variable {K : Type} [Field K] [NumberField K]
  (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
local notation "Kv" => v.adicCompletion K
local notation "O" => v.adicCompletionIntegers K

variable [IsAdicComplete (maximalIdeal (v.adicCompletionIntegers K))
  (v.adicCompletionIntegers K)]
local notation "I" => localInertiaGroup v

variable (p : ℕ) [Fact p.Prime] [CharP (ResidueField (v.adicCompletionIntegers K)) p]
  {X Y : FF (v.adicCompletionIntegers K) (v.adicCompletion K)}
  [Module (ZMod p) X.Points]

/-- Small ramification makes every generic isomorphism from a p-killed model integral. -/
theorem ModelHom.surjective_of_local_prime_field
    (he : RaynaudParameters.order (p : O) < p - 1)
    (g : ModelHom X Y) (hg : Function.Bijective (genericHom g)) : Function.Surjective g := by
  let L := InertiaDescent.field (X := X.Points) I
  let S := IntegralClosure O L
  let : HenselianLocalRing S := inertiaDescentIntegers_henselian (X := X.Points) v
  let : FaithfulSMul O L := (faithfulSMul_iff_algebraMap_injective O L).mpr (by
    rw [IsScalarTower.algebraMap_eq O Kv L]
    exact (algebraMap Kv L).injective.comp (IsFractionRing.injective O Kv))
  let : FaithfulSMul O S := inferInstance
  let : Module.IsTorsionFree O S :=
    (Module.isTorsionFree_iff_algebraMap_injective).mpr
      (FaithfulSMul.algebraMap_injective O S)
  let : Module.Flat O S := inferInstance
  let : Module.FaithfullyFlat O S := Module.FaithfullyFlat.of_isIntegral_of_isDomain
  let : CharZero L := charZero_of_injective_algebraMap (algebraMap Kv L).injective
  let : CharP (ResidueField S) p := charP_of_injective_algebraMap
    (algebraMap (ResidueField O) (ResidueField S)).injective p
  obtain ⟨n, hX⟩ := exists_scalarFiltration_inertiaDescent v X p
  let e : GenericGaloisHom (X.restrictedScalarExtension S L) (X.scalarExtension S L) :=
    (X.restrictedScalarExtension S L).inversePoints
  have hXS : (X.scalarExtension S L).HasScalarFiltration p n :=
    hX.of_generic_bijective e (X.restrictedScalarExtension S L).pointsEquiv.symm.bijective
  obtain ⟨π, hπ⟩ := exists_irreducible O
  have hπS := inertiaDescentIntegers_irreducible (X := X.Points) v hπ
  have hp : (p : O) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne p)
  have heS : RaynaudParameters.order (p : S) < p - 1 := by
    have h := RaynaudParameters.order_map_of_uniformizer (algebraMap O S) hπ hπS hp
    simpa only [map_natCast] using h.trans_lt he
  have h := (g.scalarExtension S L).surjective_of_henselian_scalarFiltration p heS hXS
    (g.generic_bijective_scalarExtension S L hg)
  exact (Module.FaithfullyFlat.lTensor_surjective_iff_surjective O S g.toAlgHom.toLinearMap).mp h

omit [Module (ZMod p) X.Points] in
/-- An annihilation equation constructs the prime-field module used by local rigidity. -/
theorem ModelHom.surjective_of_local_killed
    (he : RaynaudParameters.order (p : O) < p - 1) (hX : ∀ x : X.Points, p • x = 0)
    (g : ModelHom X Y) (hg : Function.Bijective (genericHom g)) : Function.Surjective g := by
  let : Module (ZMod p) X.Points := AddCommGroup.zmodModule hX
  exact g.surjective_of_local_prime_field v p he hg

end ThreeAdicPlan
