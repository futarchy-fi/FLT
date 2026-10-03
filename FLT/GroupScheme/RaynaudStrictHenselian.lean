/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.RaynaudResidueClosure
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Localization.Integral

/-!
# A strict Henselian DVR in the prescribed closure

The constructed unramified union is integral and faithfully flat over the base,
is Henselian with separably closed residue field, and preserves the uniformizer.
Its fraction field embeds compatibly in the same closure.
-/

@[expose] public noncomputable section

open IsLocalRing

namespace RaynaudParameters

variable {R Ω : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [HenselianLocalRing R] [Field Ω] [Algebra R Ω] [FaithfulSMul R Ω] {π : R}

/-- Every element of the union is integral, since it belongs to a finite stage. -/
theorem unramifiedUnion_integral (hπ : Irreducible π) :
    Algebra.IsIntegral R (unramifiedUnion (Ω := Ω) π) := by
  let := UnramifiedStage.nonempty (Ω := Ω) hπ
  constructor
  intro x
  obtain ⟨S, hx⟩ := exists_stage_of_mem_iSup
    (fun S : UnramifiedStage (Ω := Ω) π ↦ S.1) UnramifiedStage.directed x
  let i : S.1 →ₐ[R] unramifiedUnion (Ω := Ω) π := Subalgebra.inclusion (le_iSup _ S)
  exact (Algebra.IsIntegral.isIntegral (R := R) (⟨x, hx⟩ : S.1)).map i

/-- The uniformizer is still irreducible in the constructed union. -/
theorem unramifiedUnion_uniformizer (hπ : Irreducible π) :
    Irreducible (algebraMap R (unramifiedUnion (Ω := Ω) π) π) := by
  let := UnramifiedStage.nonempty (Ω := Ω) hπ
  exact irreducible_in_iSup _ UnramifiedStage.directed π UnramifiedStage.uniformizer

/-- Construct the strict Henselian DVR and its compatible separable fraction field.
No family of stages, residue closure, or field extension is supplied as input. -/
theorem exists_strict_henselian_unramified_tower
    {K : Type*} [Field K] [PerfectField K] [Algebra R K] [IsFractionRing R K]
    [Algebra K Ω] [IsScalarTower R K Ω] [IsAlgClosed Ω] (hπ : Irreducible π) :
    ∃ (A : Subalgebra R Ω) (_ : IsDiscreteValuationRing A) (_ : HenselianLocalRing A)
      (_ : IsSepClosed (ResidueField A)) (_ : Algebra.IsIntegral R A)
      (_ : Module.FaithfullyFlat R A) (_ : IsLocalHom (algebraMap R A))
      (_ : Algebra.IsSeparable (ResidueField R) (ResidueField A))
      (_ : Algebra K (FractionRing A))
      (_ : IsScalarTower R K (FractionRing A)) (_ : Algebra.IsAlgebraic K (FractionRing A))
      (_ : Algebra.IsSeparable K (FractionRing A)) (e : FractionRing A →ₐ[K] Ω),
      Irreducible (algebraMap R A π) ∧
      (maximalIdeal R).map (algebraMap R A) = maximalIdeal A ∧
      (∀ a : A, e (algebraMap A (FractionRing A) a) = (a : Ω)) := by
  let A := unramifiedUnion (Ω := Ω) π
  let hD := unramifiedUnion_dvr (Ω := Ω) hπ
  let hH := unramifiedUnion_henselian (Ω := Ω) hπ
  let hC := unramifiedUnion_residue_isSepClosed (Ω := Ω) hπ
  let hI := unramifiedUnion_integral (Ω := Ω) hπ
  let : FaithfulSMul R A := (faithfulSMul_iff_algebraMap_injective R A).mpr
    (fun _ _ h ↦ FaithfulSMul.algebraMap_injective R Ω (congrArg Subtype.val h))
  let hF : Module.FaithfullyFlat R A := inferInstance
  let hLocal : IsLocalHom (algebraMap R A) := inferInstance
  have hResidueSep : Algebra.IsSeparable (ResidueField R) (ResidueField A) := by
    let := UnramifiedStage.nonempty (Ω := Ω) hπ
    constructor
    intro z
    obtain ⟨x, rfl⟩ := residue_surjective z
    obtain ⟨S, hx⟩ := exists_stage_of_mem_iSup
      (fun S : UnramifiedStage (Ω := Ω) π ↦ S.1) UnramifiedStage.directed x
    let : FaithfulSMul R S.1 := (faithfulSMul_iff_algebraMap_injective R S.1).mpr
      (fun _ _ h ↦ FaithfulSMul.algebraMap_injective R Ω (congrArg Subtype.val h))
    let i : S.1 →ₐ[R] A := Subalgebra.inclusion (le_iSup _ S)
    let : IsLocalHom i := unramifiedUnion_local_inclusion hπ S
    let f := ResidueField.mapAlgHom' i
    exact (Algebra.IsSeparable.isSeparable (ResidueField R) (residue S.1 ⟨x, hx⟩)).map f f.injective
  have hmax : (maximalIdeal R).map (algebraMap R A) = maximalIdeal A := by
    rw [hπ.maximalIdeal_eq, (unramifiedUnion_uniformizer (Ω := Ω) hπ).maximalIdeal_eq,
      Ideal.map_span, Set.image_singleton]
  let L := FractionRing A
  have hinj : Function.Injective (algebraMap R L) :=
    (IsFractionRing.injective A L).comp (FaithfulSMul.algebraMap_injective R A)
  let hKL : Algebra K L := (IsFractionRing.lift hinj : K →+* L).toAlgebra
  let hT : IsScalarTower R K L := .of_algebraMap_eq fun r ↦
    (IsFractionRing.lift_algebraMap hinj r).symm
  let hAlg : Algebra.IsAlgebraic K L := isAlgebraic_of_isFractionRing R A K L
  let hSep : Algebra.IsSeparable K L := inferInstance
  let eR : L →ₐ[R] Ω := IsFractionRing.liftAlgHom (g := A.val) Subtype.val_injective
  have hcomm : eR.toRingHom.comp (algebraMap K L) = algebraMap K Ω := by
    apply IsFractionRing.ringHom_ext (A := R)
    intro r
    simp only [RingHom.comp_apply, ← IsScalarTower.algebraMap_apply R K L,
      ← IsScalarTower.algebraMap_apply R K Ω]
    exact eR.commutes r
  let e : L →ₐ[K] Ω := { eR.toRingHom with commutes' := RingHom.congr_fun hcomm }
  exact ⟨A, hD, hH, hC, hI, hF, hLocal, hResidueSep, hKL, hT, hAlg, hSep, e,
    unramifiedUnion_uniformizer hπ, hmax,
    fun a ↦ IsFractionRing.lift_algebraMap (g := A.val.toRingHom) Subtype.val_injective a⟩

end RaynaudParameters
