/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.EllipticCurve.PointReductionHom
public import FLT.EllipticCurve.PointTransport
public import FLT.EllipticCurve.Torsion
public import FLT.FreyCurve.Serre.LocalResidue
public import Mathlib.LinearAlgebra.Dual.Lemmas


/-!
# Specialization of local geometric torsion

Good reduction gives a surjective, inertia-invariant linear map from geometric
integer torsion to geometric special-fiber torsion. The construction compares the
integral model over the local algebraic closure with the canonical residue-field
algebraic closure, including the coordinate action of local inertia.

For prime torsion, a nontrivial special fiber then supplies a nonzero
inertia-invariant functional. Supersingular exclusion from a Galois-stable line
is a separate input and is not asserted here.
-/

@[expose] public section

open NumberField ValuativeRel IsLocalRing
attribute [local instance] completionValuativeRel completion_isNonarchimedeanLocalField
attribute [local instance 2000] IsDedekindDomain.HeightOneSpectrum.instAlgebraAdicCompletion
/-- Classical equality for coordinates of local geometric points. -/
noncomputable local instance goodReductionSpecializationDecidableEq (α : Type*) : DecidableEq α :=
  Classical.typeDecidableEq α
set_option quotPrecheck false
namespace WeierstrassCurve
variable {K : Type*} [Field K] [NumberField K]
variable (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
local notation "Kv" => v.adicCompletion K
local notation "R" => 𝒪[Kv]
local notation "Ω" => AlgebraicClosure Kv
local notation "κ" => ResidueField R
local notation "κbar" => AlgebraicClosure κ
local notation "A" => localClosureValuation v

/-- Specialization on positive integer torsion is surjective and inertia-invariant. -/
theorem exists_torsion_specialization_of_goodReduction (E : WeierstrassCurve Kv) [E.IsElliptic]
    [E.HasGoodReduction R] (n : ℕ) (hn : 0 < n) :
    ∃ red : (E.map (algebraMap Kv Ω)).nTorsion n →ₗ[ZMod n]
        ((E.reduction R).map (algebraMap κ κbar)).nTorsion n,
      Function.Surjective red ∧
      ∀ σ ∈ localInertiaGroup v, ∀ x, red (E.galoisRep n hn σ x) = red x := by
  let W := (E.integralModel R).map (localClosureIntegerMap v)
  have hgen : W.map (algebraMap A Ω) = E.map (algebraMap Kv Ω) :=
    localClosure_integralModel_generic v E
  have hspec : (W.map (residue A)).map (localClosureResidueCanonicalEquiv v).toRingHom =
      (E.reduction R).map (algebraMap κ κbar) := localClosure_integralModel_special v E
  have : (E.reduction R).IsElliptic :=
    (hasGoodReduction_iff_isElliptic_reduction R (W := E)).mp inferInstance
  have : (W.map (algebraMap A Ω)).IsElliptic := hgen.symm ▸ inferInstance
  have : (W.map (residue A)).IsElliptic := by
    have hh : ((W.map (residue A)).map
        (localClosureResidueCanonicalEquiv v).toRingHom).IsElliptic := hspec.symm ▸ inferInstance
    rw [isElliptic_iff, map_Δ, isUnit_iff_ne_zero] at hh
    rw [isElliptic_iff, isUnit_iff_ne_zero]
    exact fun hz => hh (by rw [hz, map_zero])
  let source : (E.map (algebraMap Kv Ω)).nTorsion n ≃+
      Submodule.torsionBy ℤ (W.map (algebraMap A Ω)).toAffine.Point (n : ℤ) :=
    TorsionCardinality.congr (Affine.Point.equivOfEq hgen.symm) n
  let target : Submodule.torsionBy ℤ (W.map (residue A)).toAffine.Point (n : ℤ) ≃+
      ((E.reduction R).map (algebraMap κ κbar)).nTorsion n :=
    TorsionCardinality.congr
      ((Affine.Point.mapRingEquiv (W.map (residue A)) (localClosureResidueCanonicalEquiv v)).trans
        (Affine.Point.equivOfEq hspec)) n
  let red := (target.toAddMonoidHom.comp ((W.reduceTorsionAddHom A n).comp
    source.toAddMonoidHom)).toZModLinearMap n
  refine ⟨red, ?_, ?_⟩
  · exact target.surjective.comp ((W.reduceTorsionAddHom_surjective A hn).comp source.surjective)
  · intro σ hσ P
    change target (W.reduceTorsion A n (source (E.galoisRep n hn σ P))) =
      target (W.reduceTorsion A n (source P))
    apply congrArg target
    apply Subtype.ext
    change W.reducePoint A (Affine.Point.equivOfEq hgen.symm (E.galoisRep n hn σ P).val) =
      W.reducePoint A (Affine.Point.equivOfEq hgen.symm P.val)
    have hinv (P₀ : (E.map (algebraMap Kv Ω)).toAffine.Point) :
        W.reducePoint A (Affine.Point.equivOfEq hgen.symm
          (Affine.Point.map (W' := E) σ.toAlgHom P₀)) =
        W.reducePoint A (Affine.Point.equivOfEq hgen.symm P₀) := by
      cases P₀ with
      | zero => rfl
      | some x y h =>
        change W.reducePoint A (Affine.Point.equivOfEq hgen.symm
          (.some (σ x) (σ y) _)) = W.reducePoint A (Affine.Point.equivOfEq hgen.symm (.some x y h))
        erw [Affine.Point.equivOfEq_some, Affine.Point.equivOfEq_some]
        exact W.reducePoint_some_inertia A (localClosureDecomposition v σ)
          (localClosureDecomposition_mem_inertia v σ hσ) _ _
    exact hinv P.val

/-- Nontrivial special-fiber prime torsion gives a nonzero inertia-invariant functional. -/
theorem exists_inertiaInvariant_functional_of_nontrivial_reduction
    (E : WeierstrassCurve Kv) [E.IsElliptic] [E.HasGoodReduction R]
    (p : ℕ) (hp : p.Prime)
    [Nontrivial (((E.reduction R).map (algebraMap κ κbar)).nTorsion p)] :
    let : Fact p.Prime := ⟨hp⟩
    ∃ q : (E.map (algebraMap Kv Ω)).nTorsion p →ₗ[ZMod p] ZMod p,
      q ≠ 0 ∧ ∀ σ ∈ localInertiaGroup v, ∀ x, q (E.galoisRep p hp.pos σ x) = q x := by
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨red, hsurj, hinv⟩ := exists_torsion_specialization_of_goodReduction v E p hp.pos
  obtain ⟨y, hy⟩ := exists_ne (0 : ((E.reduction R).map (algebraMap κ κbar)).nTorsion p)
  have : Module.Free (ZMod p) (((E.reduction R).map (algebraMap κ κbar)).nTorsion p) :=
    Module.Free.of_divisionRing _ _
  have : Module.Projective (ZMod p) (((E.reduction R).map (algebraMap κ κbar)).nTorsion p) :=
    Module.Projective.of_free
  obtain ⟨f, hf⟩ := Module.Projective.exists_dual_ne_zero (ZMod p) hy
  refine ⟨f.comp red, ?_, ?_⟩
  · obtain ⟨x, hx⟩ := hsurj y
    intro hz
    apply hf
    simpa only [LinearMap.comp_apply, hx, LinearMap.zero_apply] using LinearMap.congr_fun hz x
  · intro σ hσ x
    exact congrArg f (hinv σ hσ x)
end WeierstrassCurve
