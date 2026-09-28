/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GaloisRepresentation.HardlyRamified.ResidualPointModule
public import FLT.GroupScheme.FiniteFlatModelBaseChange
public import FLT.GroupScheme.GlobalModelAwayTwo

/-!
# Global models of hardly ramified residual representations

Transport the finite flat model at the rational prime three to the three-adic
presentation, then patch it with the unramified model away from two and three.
-/

@[expose] public noncomputable section

attribute [local instance 2000] IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
  IsDedekindDomain.HeightOneSpectrum.instAlgebraAdicCompletion

namespace ThreeAdicPlan

/-- The rational place above three. -/
abbrev threeAdicPlace := Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat

/-- The completion at three and its integer ring have compatible three-adic presentations. -/
theorem exists_completionThreeEquiv :
    ∃ e : threeAdicPlace.adicCompletion ℚ ≃+* ℚ_[3],
      ∃ eR : threeAdicPlace.adicCompletionIntegers ℚ ≃+* ℤ_[3],
        ∀ x : threeAdicPlace.adicCompletionIntegers ℚ, (eR x : ℚ_[3]) = e x := by
  let instPrime : Fact (Nat.Prime (Rat.HeightOneSpectrum.primesEquiv threeAdicPlace : ℕ)) :=
    ⟨(Rat.HeightOneSpectrum.primesEquiv threeAdicPlace).property⟩
  have h : ∃ e : threeAdicPlace.adicCompletion ℚ ≃+*
      ℚ_[↑(Rat.HeightOneSpectrum.primesEquiv threeAdicPlace)],
      ∃ eR : threeAdicPlace.adicCompletionIntegers ℚ ≃+*
        ℤ_[↑(Rat.HeightOneSpectrum.primesEquiv threeAdicPlace)],
        ∀ x : threeAdicPlace.adicCompletionIntegers ℚ,
          (eR x : ℚ_[↑(Rat.HeightOneSpectrum.primesEquiv threeAdicPlace)]) = e x :=
    ⟨(Rat.HeightOneSpectrum.adicCompletion.padicEquiv threeAdicPlace).toRingEquiv,
      (Rat.HeightOneSpectrum.adicCompletionIntegers.padicIntEquiv threeAdicPlace).toRingEquiv,
      fun _ ↦ rfl⟩
  have hp : (Rat.HeightOneSpectrum.primesEquiv threeAdicPlace : ℕ) = 3 :=
    congrArg Subtype.val (primesEquiv_ratPrime 3 Nat.prime_three)
  have transport (p : ℕ) [Fact p.Prime] (hp : p = 3)
      (h : ∃ e : threeAdicPlace.adicCompletion ℚ ≃+* ℚ_[p],
        ∃ eR : threeAdicPlace.adicCompletionIntegers ℚ ≃+* ℤ_[p],
          ∀ x : threeAdicPlace.adicCompletionIntegers ℚ, (eR x : ℚ_[p]) = e x) :
      ∃ e : threeAdicPlace.adicCompletion ℚ ≃+* ℚ_[3],
        ∃ eR : threeAdicPlace.adicCompletionIntegers ℚ ≃+* ℤ_[3],
          ∀ x : threeAdicPlace.adicCompletionIntegers ℚ, (eR x : ℚ_[3]) = e x := by
    subst p
    exact h
  exact transport _ hp h

/-- Two successive local restrictions agree with the direct restriction up to a
bijective equivariant point map, accounting for the chosen closure embeddings. -/
theorem localThreeRestriction_comparison (W : FiniteContinuousGaloisModule)
    (e : threeAdicPlace.adicCompletion ℚ →+* ℚ_[3]) :
    ∃ q : ((W.restrict (algebraMap ℚ (threeAdicPlace.adicCompletion ℚ))).restrict e) →+[
      Field.absoluteGaloisGroup ℚ_[3]] W.localAtThree, Function.Bijective q := by
  let f := algebraMap ℚ (threeAdicPlace.adicCompletion ℚ)
  let f₃ := algebraMap ℚ ℚ_[3]
  obtain ⟨a, ha⟩ := exists_global_embedding_comparison
    ((AlgebraicClosure.map e).comp (AlgebraicClosure.map f)) (AlgebraicClosure.map f₃)
  have he (σ : Field.absoluteGaloisGroup ℚ_[3]) :
      a * Field.absoluteGaloisGroup.map f (Field.absoluteGaloisGroup.map e σ) =
        Field.absoluteGaloisGroup.map f₃ σ * a := by
    ext x
    apply (AlgebraicClosure.map f₃).injective
    change AlgebraicClosure.map f₃ (a (Field.absoluteGaloisGroup.map f
      (Field.absoluteGaloisGroup.map e σ) x)) =
        AlgebraicClosure.map f₃ (Field.absoluteGaloisGroup.map f₃ σ (a x))
    rw [ha, Field.absoluteGaloisGroup.lift_map]
    change AlgebraicClosure.map e (AlgebraicClosure.map f
      (Field.absoluteGaloisGroup.map f (Field.absoluteGaloisGroup.map e σ) x)) = _
    rw [Field.absoluteGaloisGroup.lift_map, Field.absoluteGaloisGroup.lift_map, ha]
    rfl
  let t : W →+ W :=
    { toFun := fun x ↦ a • x
      map_zero' := smul_zero a
      map_add' := smul_add a }
  have ht (σ : Field.absoluteGaloisGroup ℚ_[3]) (x : W) :
      t (Field.absoluteGaloisGroup.map f (Field.absoluteGaloisGroup.map e σ) • x) =
        Field.absoluteGaloisGroup.map f₃ σ • t x := by
    change a • (Field.absoluteGaloisGroup.map f
      (Field.absoluteGaloisGroup.map e σ) • x) =
        Field.absoluteGaloisGroup.map f₃ σ • (a • x)
    rw [← mul_smul, he, mul_smul]
  let q : ((W.restrict f).restrict e) →+[Field.absoluteGaloisGroup ℚ_[3]] W.localAtThree :=
    { t with map_smul' := ht }
  have htbij : Function.Bijective t := MulAction.bijective a
  exact ⟨q, htbij⟩

/-- A model over the completion's integer ring transports to a model over `ℤ₃`. -/
theorem localThreeModel_transport (W : FiniteContinuousGaloisModule)
    (M : HasFiniteFlatModel (threeAdicPlace.adicCompletionIntegers ℚ)
      (W.restrict (algebraMap ℚ (threeAdicPlace.adicCompletion ℚ)))) :
    Nonempty (HasFiniteFlatModel ℤ_[3] W.localAtThree) := by
  obtain ⟨e, eR, hR⟩ := exists_completionThreeEquiv
  let R := threeAdicPlace.adicCompletionIntegers ℚ
  let K := threeAdicPlace.adicCompletion ℚ
  let instAlgebraRS : Algebra R ℤ_[3] := eR.toRingHom.toAlgebra
  let instAlgebraKL : Algebra K ℚ_[3] := e.toRingHom.toAlgebra
  let instAlgebraRL : Algebra R ℚ_[3] := Algebra.compHom ℚ_[3] eR.toRingHom
  let instTowerRSL : IsScalarTower R ℤ_[3] ℚ_[3] :=
    IsScalarTower.of_algebraMap_eq' rfl
  let instTowerRKL : IsScalarTower R K ℚ_[3] :=
    IsScalarTower.of_algebraMap_eq fun x ↦ hR x
  let N := M.baseChange (S := ℤ_[3]) (L := ℚ_[3])
  obtain ⟨q, hq⟩ := localThreeRestriction_comparison W e.toRingHom
  apply (nonempty_hasFiniteFlatModel_iff _).mpr
  exact N.isFiniteFlat.map _ _ _ _ q hq

/-- Every hardly ramified residual representation has a global category-D model. -/
theorem residualPointModule_globalModel
    {k : Type*} [Field k] [Finite k] [Algebra ℤ_[3] k]
    [TopologicalSpace k] [DiscreteTopology k]
    {V : Type} [AddCommGroup V] [Module k V] [Module.Finite k V]
    (hV : Module.rank k V = 2) (ρ : GaloisRep ℚ k V)
    (hρ : GaloisRepresentation.IsHardlyRamified (show Odd 3 by decide) hV ρ) :
    Nonempty (DModel (residualPointModule ρ)) := by
  obtain ⟨M⟩ := residualPointModule_localModel ρ threeAdicPlace hρ.isFlat
  obtain ⟨M₃⟩ := localThreeModel_transport _ M
  obtain ⟨N⟩ := global_model_away_two _ M₃ (residualPointModule_unramified hV ρ hρ)
  exact ⟨{ toModelOverZInvTwo := N
           inCategoryD := residualPointModule_inCategoryD hV ρ hρ N }⟩

end ThreeAdicPlan
