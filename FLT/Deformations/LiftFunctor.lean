/-
Copyright (c) 2025 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang, Kevin Buzzard, Ruben Van de Velde
-/
module

public import FLT.Deformations.Categories
public import FLT.Deformations.Subfunctor
public import FLT.Deformations.RepresentationTheory.GaloisRep
public import Mathlib.NumberTheory.Cyclotomic.CyclotomicCharacter
public import Mathlib.RingTheory.LocalRing.Quotient

/-!
# The functor of continuous representations

For a profinite group `G` and a proartinian local ring `𝓞`, the functor
`repnFunctor n G 𝓞` sends a proartinian `𝓞`-algebra `R` to the set of
continuous representations `G → GLₙ(R)`.
-/

@[expose] public section

open CategoryTheory IsLocalRing

namespace Deformation

universe u

variable {n : Type} [Fintype n] [DecidableEq n] (G : Type u) [Group G] [TopologicalSpace G]
variable (𝓞 : Type u) [CommRing 𝓞] [IsLocalRing 𝓞]
variable {K : Type u} [Field K] [NumberField K]

local notation3 "Γ" K:max => Field.absoluteGaloisGroup K
local notation3 K:max "ᵃˡᵍ" => AlgebraicClosure K
local notation "Ω" K => IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)

open scoped TypeCat TensorProduct
variable (n) in
/-- `repnFunctor n G 𝓞` is the functor taking `R` to continuous reps `G → GLₙ(R)`. -/
def repnFunctor : ProartinianCat 𝓞 ⥤ Type u where
  obj R := G →ₜ* GL n R
  map {R S} f := ↾ (fun ρ ↦ .comp (Units.mapₜ f.hom.mapMatrix.toContinuousMonoidHom) ρ)

omit [IsLocalRing 𝓞] in
@[simp]
lemma repnFunctor_map {R S : ProartinianCat 𝓞} (f : R ⟶ S) (ρ : G →ₜ* GL n R) (x : G) :
    DFunLike.coe (F := G →ₜ* GL n S) ((repnFunctor n G 𝓞).map f ρ) x =
      Matrix.GeneralLinearGroup.map (n := n) f.hom.toRingHom (ρ x) := rfl

variable {G 𝓞} in
/-- Turn an element in `repnFunctor` into an actual `Representation`. -/
def toRepresentation {R} (ρ : (repnFunctor n G 𝓞).obj R) :
    Representation R G (n → R) :=
  (Units.coeHom _).comp (Matrix.GeneralLinearGroup.toLin.toMonoidHom.comp ρ.toMonoidHom)

variable {G 𝓞} in
/-- Turn an element in `repnFunctor` into an actual `GaloisRep`. -/
noncomputable
def toFramedGaloisRep {R} (ρ : (repnFunctor n (Γ K) 𝓞).obj R) :
    FramedGaloisRep K R n :=
  FramedGaloisRep.GL.symm ρ

set_option backward.isDefEq.respectTransparency.types false in
omit [IsLocalRing 𝓞] [NumberField K] in
lemma toFramedGaloisRep_map {R S : ProartinianCat 𝓞} (f : R ⟶ S)
    (ρ : (repnFunctor n (Γ K) 𝓞).obj R) :
    toFramedGaloisRep ((repnFunctor n (Γ K) 𝓞).map f ρ) =
      (toFramedGaloisRep ρ).baseChange f.hom f.hom.cont := by
  apply FramedGaloisRep.GL.injective
  ext
  simp [toFramedGaloisRep]

variable (n)

set_option backward.isDefEq.respectTransparency false in
/-- `repnQuotFunctor n G 𝓞` is the functor taking `R` to continuous reps `G → GLₙ(R)` up to
conjugation by some `γ` in the kernel of `GLₙ(R) → GLₙ(𝕜)`. -/
noncomputable
def repnQuotFunctor : ProartinianCat 𝓞 ⥤ Type u where
  obj R := MulAction.orbitRel.Quotient ((Matrix.GeneralLinearGroup.map (n := n)
    (ProartinianCat.toResidueField R).hom.toRingHom).ker.comap (ConjAct.ofConjAct.toMonoidHom))
    (G →ₜ* GL n R)
  map {R S} f := ↾Quotient.map ((repnFunctor n G 𝓞).map f) (by
    rintro _ ρ ⟨⟨g, hg⟩, rfl⟩
    refine ⟨⟨.toConjAct (Matrix.GeneralLinearGroup.map f.hom.toRingHom g.ofConjAct), ?_⟩, ?_⟩
    · simpa [← Matrix.GeneralLinearGroup.map_comp_apply, ← Matrix.GeneralLinearGroup.map_comp,
        ← RingHom.coe_comp, ← ContinuousAlgHom.coe_comp,
        -AlgHomClass.toRingHom_toAlgHom, ← AlgHom.comp_toRingHom, ← ProartinianCat.hom_comp,
        Subsingleton.elim _ R.toResidueField]
    · obtain ⟨g, rfl⟩ := ConjAct.toConjAct.surjective g
      ext1 γ
      simp [ConjAct.toConjAct_smul, ← map_inv, -ConjAct.ofConjAct_inv, ← map_mul])
  map_id _ := by ext ⟨_⟩; rfl
  map_comp _ _ := by ext ⟨_⟩; rfl

/-- The quotient map taking representations to "representations up to equivalence". -/
noncomputable
def toRepnQuot : repnFunctor n G 𝓞 ⟶ repnQuotFunctor n G 𝓞 where
  app _ := ↾Quotient.mk''
  naturality _ _ _ := rfl

/-- `liftFunctor n G 𝓞` is the functor taking `R` to lifts `G → GLₙ(R)` of `ρ : G → GLₙ(𝕜)`. -/
noncomputable
def liftFunctor (ρ : (repnFunctor n G 𝓞).obj .residueField) : Subfunctor (repnFunctor n G 𝓞) :=
  .ofIsTerminal _ ProartinianCat.isTerminalResidueField {ρ}

/-- `deformationFunctor n G 𝓞` is the functor taking `R` to lifts `G → GLₙ(R)` of `ρ : G → GLₙ(𝕜)`,
up to conjugation by some `γ` in the kernel of `GLₙ(R) → GLₙ(𝕜)`. -/
noncomputable
def deformationFunctor (ρ : (repnFunctor n G 𝓞).obj .residueField) :
    Subfunctor (repnQuotFunctor n G 𝓞) :=
  .ofIsTerminal _ ProartinianCat.isTerminalResidueField {(toRepnQuot n G 𝓞).app _ ρ}

/-- The subfunctor of flat lifts. This probably only makes sense when `𝓞` is `v`-adic. -/
noncomputable
def flatFunctor (v : Ω K) : Subfunctor (repnFunctor n (Γ K) 𝓞) where
  obj R := { ρ | (toFramedGaloisRep ρ).IsFlatAt v }
  map {R S} f ρ hρ := by
    change (toFramedGaloisRep ((repnFunctor n (Γ K) 𝓞).map f ρ)).IsFlatAt v
    change (toFramedGaloisRep ρ).IsFlatAt v at hρ
    rw [toFramedGaloisRep_map]
    constructor
    intro J hJ
    by_cases hJtop : J = ⊤
    · subst J
      let e := TensorProduct.piScalarRight S (S ⧸ (⊤ : Ideal S))
        (S ⧸ (⊤ : Ideal S)) n
      let : Subsingleton
          (((GaloisRep.baseChange (S ⧸ (⊤ : Ideal S))
            ((toFramedGaloisRep ρ).baseChange f.hom f.hom.cont)).toLocal v).Space) :=
        ⟨fun x y ↦ e.injective (Subsingleton.elim _ _)⟩
      exact GaloisModule.IsFiniteFlat.of_subsingleton _ _ _ _
    by_cases hn : Nonempty n
    swap
    · let : IsEmpty n := not_nonempty_iff.mp hn
      let e := TensorProduct.piScalarRight S (S ⧸ J) (S ⧸ J) n
      let : Subsingleton
          (((GaloisRep.baseChange (S ⧸ J)
            ((toFramedGaloisRep ρ).baseChange f.hom f.hom.cont)).toLocal v).Space) :=
        ⟨fun x y ↦ e.injective (Subsingleton.elim _ _)⟩
      exact GaloisModule.IsFiniteFlat.of_subsingleton _ _ _ _
    let I : Ideal R := J.comap f.hom.toRingHom
    have hI : IsOpen (I : Set R) := by
      change IsOpen (f.hom ⁻¹' (J : Set S))
      exact hJ.preimage f.hom.cont
    have hflat := hρ.cond I hI
    have hItop : I ≠ ⊤ := by
      intro h
      apply hJtop
      have h1 : (1 : R) ∈ I := h.symm ▸ trivial
      have h1' : (1 : S) ∈ J := by simpa [I] using h1
      exact Ideal.eq_top_of_isUnit_mem J h1' isUnit_one
    let : Nontrivial (R ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hItop
    let eI := TensorProduct.piScalarRight R (R ⧸ I) (R ⧸ I) n
    let X := (((GaloisRep.baseChange (R ⧸ I) (toFramedGaloisRep ρ)).toLocal v).Space)
    let : Finite X := GaloisModule.IsFiniteFlat.finite _ _ _ _ hflat
    let sourceAction : DistribMulAction
        (Field.absoluteGaloisGroup
          (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v))
        ((R ⧸ I) ⊗[R] (n → R)) :=
      inferInstanceAs (DistribMulAction
        (Field.absoluteGaloisGroup
          (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v)) X)
    let := sourceAction
    let i₀ : n := Classical.choice hn
    let embed : (R ⧸ I) → X := fun a ↦ eI.symm (Pi.single i₀ a)
    have hembed : Function.Injective embed := by
      intro a b hab
      have hab' := congrArg (fun x ↦ eI x i₀) hab
      simpa [embed, i₀] using hab'
    let : Finite (R ⧸ I) := Finite.of_injective embed hembed
    let : Finite (ResidueField (R ⧸ I)) :=
      Finite.of_surjective (residue (R ⧸ I)) IsLocalRing.residue_surjective
    let : IsLocalHom (Ideal.Quotient.mk I) :=
      IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
    let : IsLocalHom (algebraMap 𝓞 (R ⧸ I)) := by
      change IsLocalHom ((Ideal.Quotient.mk I).comp (algebraMap 𝓞 R))
      infer_instance
    let eR := IsResidueAlgebra.algEquiv 𝓞 (R ⧸ I)
    let : Finite (ResidueField 𝓞) := Finite.of_injective eR eR.injective
    let : Nontrivial (S ⧸ J) := Ideal.Quotient.nontrivial_iff.mpr hJtop
    let : IsLocalHom (Ideal.Quotient.mk J) :=
      IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
    let : IsLocalHom (algebraMap 𝓞 (S ⧸ J)) := by
      change IsLocalHom ((Ideal.Quotient.mk J).comp (algebraMap 𝓞 S))
      infer_instance
    let eS := IsResidueAlgebra.algEquiv 𝓞 (S ⧸ J)
    let : Finite (ResidueField (S ⧸ J)) := Finite.of_surjective eS eS.surjective
    let : IsArtinianRing (S ⧸ J) := IsProartinian.isArtinianRing_quotient J hJ
    have hpow : ∃ m, maximalIdeal (S ⧸ J) ^ m ≤ (⊥ : Ideal (S ⧸ J)) :=
      IsLocalRing.exists_maximalIdeal_pow_le_of_isArtinianRing_quotient
        (⊥ : Ideal (S ⧸ J))
    let : Finite ((S ⧸ J) ⧸ (⊥ : Ideal (S ⧸ J))) :=
      IsLocalRing.finite_quotient_iff.mpr hpow
    let : Finite (S ⧸ J) := Finite.of_surjective (RingEquiv.quotientBot (S ⧸ J))
      (RingEquiv.quotientBot (S ⧸ J)).surjective
    let g₀ : R →+* (S ⧸ J) := (Ideal.Quotient.mk J).comp f.hom.toRingHom
    let g : (R ⧸ I) →+* (S ⧸ J) := Ideal.Quotient.lift I g₀ (by
      intro x hx
      apply Ideal.Quotient.eq_zero_iff_mem.mpr
      exact hx)
    let : Algebra R (S ⧸ J) := g₀.toAlgebra
    let : Algebra (R ⧸ I) (S ⧸ J) := g.toAlgebra
    let : IsScalarTower R (R ⧸ I) (S ⧸ J) := IsScalarTower.of_algebraMap_eq fun r ↦ by
      exact (Ideal.Quotient.lift_mk I g₀ _).symm
    let : Module.Finite (R ⧸ I) (S ⧸ J) := Module.Finite.of_finite
    obtain ⟨d, ell, hell⟩ := Module.Finite.exists_fin' (R ⧸ I) (S ⧸ J)
    let Y := (((GaloisRep.baseChange (S ⧸ J)
      ((toFramedGaloisRep ρ).baseChange f.hom.toRingHom f.hom.cont)).toLocal v).Space)
    let eJ := TensorProduct.piScalarRight S (S ⧸ J) (S ⧸ J) n
    let qAdd : (Fin d → ((R ⧸ I) ⊗[R] (n → R))) →+ Y :=
      { toFun := fun x ↦ eJ.symm (fun i ↦ ell (fun k ↦ eI (x k) i))
        map_zero' := by
          apply eJ.injective
          rw [eJ.apply_symm_apply]
          ext i
          change ell (fun _ ↦ eI (0 : (R ⧸ I) ⊗[R] (n → R)) i) = 0
          change ell 0 = 0
          exact ell.map_zero
        map_add' := by
          intro x y
          apply eJ.injective
          rw [eJ.apply_symm_apply]
          ext i
          change ell (fun k ↦ eI (x k + y k) i) =
            eJ (eJ.symm (fun i ↦ ell (fun k ↦ eI (x k) i)) +
              eJ.symm (fun i ↦ ell (fun k ↦ eI (y k) i))) i
          simp only [map_add, Pi.add_apply, eJ.apply_symm_apply]
          rw [← ell.map_add]
          rfl }
    let q : (Fin d → ((R ⧸ I) ⊗[R] (n → R))) →+[
        Field.absoluteGaloisGroup (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v)] Y :=
      { qAdd with
        map_smul' := by
          intro sigma x
          change qAdd (sigma • x) = sigma • qAdd x
          classical
          rw [← Finset.univ_sum_single x]
          rw [Finset.smul_sum, map_sum, map_sum, Finset.smul_sum]
          apply Finset.sum_congr rfl
          intro k _
          rw [← Pi.single_smul]
          let t : (R ⧸ I) ⊗[R] (n → R) := x k
          change qAdd (Pi.single k (sigma • t)) = sigma • qAdd (Pi.single k t)
          induction t using TensorProduct.induction_on with
          | zero =>
            rw [smul_zero, Pi.single_zero, map_zero]
            exact (smul_zero sigma).symm
          | add z w hz hw =>
            rw [smul_add, Pi.single_add, map_add, Pi.single_add, map_add, smul_add, hz, hw]
          | tmul a m =>
            have hs : sigma • (a ⊗ₜ[R] m : (R ⧸ I) ⊗[R] (n → R)) =
                a ⊗ₜ[R] ((toFramedGaloisRep ρ).toLocal v sigma m) := by
              change ((GaloisRep.baseChange (R ⧸ I)
                (toFramedGaloisRep ρ)).toLocal v) sigma (a ⊗ₜ[R] m) = _
              rfl
            rw [hs]
            let b : S ⧸ J := ell (Pi.single k a)
            let mS : n → S := fun i ↦ f.hom (m i)
            have hbase : (show Y from eJ.symm (fun i ↦ ell (fun j ↦ eI
                  (((Pi.single k (a ⊗ₜ[R] m)) :
                    Fin d → ((R ⧸ I) ⊗[R] (n → R))) j) i))) =
                (show Y from b ⊗ₜ[S] mS) := by
              apply eJ.injective
              rw [eJ.apply_symm_apply]
              ext i
              simp only [eI, eJ, TensorProduct.piScalarRight_apply,
                TensorProduct.piScalarRightHom_tmul, Pi.single_apply]
              dsimp [b, mS]
              have hcoord : (fun j ↦
                  (TensorProduct.piScalarRightHom R (R ⧸ I) (R ⧸ I) n)
                    (if j = k then a ⊗ₜ[R] m else 0) i) =
                  Pi.single k ((Ideal.Quotient.mk I (m i)) * a) := by
                ext j
                by_cases hj : j = k
                · subst j
                  simp [TensorProduct.piScalarRightHom_tmul, Algebra.smul_def]
                · simp [hj]
              rw [hcoord]
              calc
                ell (Pi.single k ((Ideal.Quotient.mk I (m i)) * a)) =
                    ell ((Ideal.Quotient.mk I (m i)) • Pi.single k a) := by
                      congr 1
                      ext j
                      simp [Pi.single_apply, smul_eq_mul]
                _ = (Ideal.Quotient.mk I (m i)) • ell (Pi.single k a) :=
                  ell.map_smul _ _
                _ = f.hom (m i) • ell (Pi.single k a) := by
                  change g (Ideal.Quotient.mk I (m i)) * ell (Pi.single k a) =
                    (Ideal.Quotient.mk J (f.hom (m i))) * ell (Pi.single k a)
                  rw [Ideal.Quotient.lift_mk]
                  rfl
            change eJ.symm (fun i ↦ ell (fun j ↦ eI
                (((Pi.single k (a ⊗ₜ[R]
                  ((toFramedGaloisRep ρ).toLocal v sigma m))) :
                    Fin d → ((R ⧸ I) ⊗[R] (n → R))) j) i)) =
              sigma • (show Y from eJ.symm (fun i ↦ ell (fun j ↦ eI
                (((Pi.single k (a ⊗ₜ[R] m)) :
                  Fin d → ((R ⧸ I) ⊗[R] (n → R))) j) i)))
            rw [hbase]
            have ht : sigma • (show Y from b ⊗ₜ[S] mS) =
                (show Y from b ⊗ₜ[S]
                  (((toFramedGaloisRep ρ).baseChange f.hom.toRingHom f.hom.cont).toLocal v
                    sigma mS)) := by
              change ((GaloisRep.baseChange (S ⧸ J)
                ((toFramedGaloisRep ρ).baseChange f.hom.toRingHom
                  f.hom.cont)).toLocal v) sigma (b ⊗ₜ[S] mS) = _
              rfl
            rw [ht]
            have hrep :
                (((toFramedGaloisRep ρ).baseChange f.hom.toRingHom f.hom.cont).toLocal v
                  sigma mS) =
                fun i ↦ f.hom ((toFramedGaloisRep ρ).toLocal v sigma m i) := by
              change (FramedGaloisRep.baseChange
                ((toFramedGaloisRep ρ).toLocal v)
                f.hom.toRingHom f.hom.cont sigma mS) = _
              ext i
              simp only [AlgHom.toRingHom_eq_coe]
              rw [← LinearMap.toMatrix'_mulVec
                (((toFramedGaloisRep ρ).toLocal v) sigma) m]
              exact (RingHom.map_mulVec f.hom.toRingHom
                (((toFramedGaloisRep ρ).toLocal v sigma).toMatrix') m i).symm
            rw [hrep]
            apply eJ.injective
            rw [eJ.apply_symm_apply]
            ext i
            simp only [eI, eJ, TensorProduct.piScalarRight_apply,
              TensorProduct.piScalarRightHom_tmul, Pi.single_apply]
            dsimp [b]
            have hcoord : (fun j ↦
                (TensorProduct.piScalarRightHom R (R ⧸ I) (R ⧸ I) n)
                  (if j = k then
                    a ⊗ₜ[R] ((toFramedGaloisRep ρ).toLocal v sigma m) else 0) i) =
                Pi.single k ((Ideal.Quotient.mk I
                  ((toFramedGaloisRep ρ).toLocal v sigma m i)) * a) := by
              ext j
              by_cases hj : j = k
              · subst j
                simp [TensorProduct.piScalarRightHom_tmul, Algebra.smul_def]
              · simp [hj]
            rw [hcoord]
            calc
              ell (Pi.single k
                  ((Ideal.Quotient.mk I
                    ((toFramedGaloisRep ρ).toLocal v sigma m i)) * a)) =
                  ell ((Ideal.Quotient.mk I
                    ((toFramedGaloisRep ρ).toLocal v sigma m i)) • Pi.single k a) := by
                    congr 1
                    ext j
                    simp [Pi.single_apply, smul_eq_mul]
              _ = (Ideal.Quotient.mk I
                    ((toFramedGaloisRep ρ).toLocal v sigma m i)) •
                  ell (Pi.single k a) := ell.map_smul _ _
              _ = f.hom ((toFramedGaloisRep ρ).toLocal v sigma m i) •
                    ell (Pi.single k a) := by
                    change g (Ideal.Quotient.mk I
                      ((toFramedGaloisRep ρ).toLocal v sigma m i)) *
                        ell (Pi.single k a) =
                      (Ideal.Quotient.mk J
                        (f.hom ((toFramedGaloisRep ρ).toLocal v sigma m i))) *
                          ell (Pi.single k a)
                    rw [Ideal.Quotient.lift_mk]
                    rfl
      }
    have hq : Function.Surjective q := by
      intro y
      choose z hz using fun i ↦ hell (eJ y i)
      let pre : Fin d → ((R ⧸ I) ⊗[R] (n → R)) :=
        fun k ↦ eI.symm (fun i ↦ z i k)
      refine ⟨pre, ?_⟩
      change (show Y from eJ.symm
        (fun i ↦ ell (fun k ↦ eI (pre k) i))) = y
      apply eJ.injective
      rw [eJ.apply_symm_apply]
      ext i
      have hfun : (fun k ↦ eI (eI.symm (fun j ↦ z j k)) i) = z i := by
        ext k
        exact congrFun (eI.apply_symm_apply (fun j ↦ z j k)) i
      change ell (fun k ↦ eI (eI.symm (fun j ↦ z j k)) i) = eJ y i
      rw [hfun]
      exact hz i
    exact GaloisModule.IsFiniteFlat.quotient _ _ _ _
      (GaloisModule.IsFiniteFlat.finPow _ _ _ _ hflat d) q hq

set_option backward.isDefEq.respectTransparency.types false in
/-- The subfunctor of unramified (at `v`) representations. -/
def unramifiedFunctor (v : Ω K) : Subfunctor (repnFunctor n (Γ K) 𝓞) where
  obj R := { ρ | (toFramedGaloisRep ρ).IsUnramifiedAt v }
  map {R S} f ρ hρ := by
    have : (toFramedGaloisRep ρ).IsUnramifiedAt v := hρ
    simp only [Set.preimage_ofPred_eq, toFramedGaloisRep_map, FramedGaloisRep.baseChange_def,
      GaloisRep.frame, Set.mem_ofPred_eq] at ⊢
    infer_instance

set_option backward.isDefEq.respectTransparency.types false in
/-- The subfunctor of representations whose trace is `2` on `ker(Iᵥ → k(v)ˣ)`. -/
def traceConditionFunctor (v : Ω K) : Subfunctor (repnFunctor (Fin 2) (Γ K) 𝓞) where
  obj R := { ρ | ∀ σ ∈ localTameAbelianInertiaGroup v,
    LinearMap.trace _ _ ((toFramedGaloisRep ρ).toLocal v σ) = 2 }
  map {R S} f ρ hρ σ hσ := by
    have := hρ σ hσ
    simp only [GaloisRep.toLocal, toFramedGaloisRep_map, FramedGaloisRep.baseChange_map] at this ⊢
    simp [FramedGaloisRep.baseChange, ← Matrix.toLin'_apply', ← AddMonoidHom.map_trace,
      ← LinearMap.toMatrix_eq_toMatrix', ← LinearMap.trace_eq_matrix_trace, this, map_ofNat]

set_option backward.isDefEq.respectTransparency.types false in
/-- The subfunctor of representations whose trace is `2` on `Iᵥ`. -/
def narrowTraceConditionFunctor (v : Ω K) : Subfunctor (repnFunctor (Fin 2) (Γ K) 𝓞) where
  obj R := { ρ | ∀ σ ∈ localInertiaGroup v,
    LinearMap.trace _ _ ((toFramedGaloisRep ρ).toLocal v σ) = 2 }
  map {R S} f ρ hρ σ hσ := by
    have := hρ σ hσ
    simp only [GaloisRep.toLocal, toFramedGaloisRep_map, FramedGaloisRep.baseChange_map] at this ⊢
    simp [FramedGaloisRep.baseChange, ← Matrix.toLin'_apply', ← AddMonoidHom.map_trace,
      ← LinearMap.toMatrix_eq_toMatrix', ← LinearMap.trace_eq_matrix_trace, this, map_ofNat]

set_option backward.isDefEq.respectTransparency.types false in
/-- The subfunctor of representations with `det = εₗ`. -/
def detConditionFunctor (l : ℕ) [Fact l.Prime] [Algebra ℤ_[l] 𝓞] :
    Subfunctor (repnFunctor n (Γ K) 𝓞) where
  obj R := { ρ | ∀ σ, (toFramedGaloisRep ρ).det σ =
    algebraMap 𝓞 R (algebraMap ℤ_[l] 𝓞 (cyclotomicCharacter (Kᵃˡᵍ) l σ)) }
  map {R S} f ρ hρ σ := by
    have := hρ σ
    simp only [toFramedGaloisRep_map, FramedGaloisRep.det_baseChange,
      ContinuousMonoidHom.comp_toFun, ContinuousMonoidHom.coe_mk, MonoidHom.coe_coe,
      RingHom.coe_coe] at this ⊢
    rw [this]
    exact f.hom.commutes ..

end Deformation
