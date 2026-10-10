/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.TensorKernelArtinian
public import Mathlib.LinearAlgebra.Isomorphisms

/-!
# Cyclic coefficients detect universal tensor exactness

For an augmented complex with flat final term, exactness with all ring
quotients implies exactness with every coefficient module. Finite generation
uses successive cyclic quotients; every tensor is supported on a finite submodule.
-/

@[expose] public noncomputable section
open TensorProduct
namespace FLT.Mazur.TensorKernelCyclic
open TensorKernelExtension TensorKernelFiniteLength
variable {R : Type} [CommRing R]
  {P M N : Type} [AddCommGroup P] [Module R P]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  (u : P →ₗ[R] M) (d : M →ₗ[R] N)
  (hquot : ∀ I : Ideal R, Function.Exact (u.lTensor (R ⧸ I)) (d.lTensor (R ⧸ I)))

include hquot

/-- Every cyclic coefficient is an actual ring quotient as a module. -/
lemma exact_of_cyclic {B : Type} [AddCommGroup B] [Module R B]
    (a : R →ₗ[R] B) (ha : Function.Surjective a) :
    Function.Exact (u.lTensor B) (d.lTensor B) :=
  exact_of_equiv u d (a.quotKerEquivOfSurjective ha) (hquot a.ker)

variable [Module.Flat R N] (hdu : d.comp u = 0)

include hdu

/-- Adding one generator gives a cyclic quotient of the original coefficient submodule. -/
lemma exact_sup_span {B : Type} [AddCommGroup B] [Module R B]
    (L : Submodule R B) (b : B)
    (hL : Function.Exact (u.lTensor L) (d.lTensor L)) :
    Function.Exact (u.lTensor ↥(L ⊔ R ∙ b)) (d.lTensor ↥(L ⊔ R ∙ b)) := by
  let V := L ⊔ R ∙ b
  let K := L.comap V.subtype
  apply exact_of_submodule u d hdu K
  · exact exact_of_equiv u d (Submodule.comapSubtypeEquivOfLe
      (show L ≤ V from le_sup_left)).symm hL
  · let v : V := ⟨b, (show R ∙ b ≤ V from le_sup_right)
      (Submodule.mem_span_singleton_self b)⟩
    let a := K.mkQ.comp (LinearMap.toSpanSingleton R V v)
    apply exact_of_cyclic u d hquot a
    intro z
    obtain ⟨w, rfl⟩ := K.mkQ_surjective z
    obtain ⟨l, hl, c, hc, he⟩ := Submodule.mem_sup.mp w.property
    obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.mp hc
    refine ⟨r, ?_⟩
    change K.mkQ (r • v) = K.mkQ w
    apply (Submodule.Quotient.eq K).mpr
    change r • b - w.val ∈ L
    rw [← he, ← hr]
    convert L.neg_mem hl using 1
    abel

/-- Every finite coefficient is built by successive cyclic extensions. -/
theorem exact_finite_coefficients (B : Type) [AddCommGroup B] [Module R B]
    [Module.Finite R B] : Function.Exact (u.lTensor B) (d.lTensor B) := by
  have h (L : Submodule R B) (hL : L.FG) :
      Function.Exact (u.lTensor L) (d.lTensor L) := by
    apply Submodule.fg_sup_span_induction (motive := fun L _ ↦
      Function.Exact (u.lTensor L) (d.lTensor L)) ?_ ?_ L hL
    · intro x
      exact ⟨fun _ ↦ ⟨0, Subsingleton.elim _ _⟩, fun _ ↦ Subsingleton.elim _ _⟩
    · intro L b _ ih
      exact exact_sup_span u d hquot hdu L b ih
  exact exact_of_equiv u d (Submodule.topEquiv : (⊤ : Submodule R B) ≃ₗ[R] B)
    (h ⊤ (Module.Finite.fg_top))

/-- Ring-quotient exactness controls arbitrary, possibly infinite, coefficients. -/
theorem exact_arbitrary_coefficients (B : Type) [AddCommGroup B] [Module R B] :
    Function.Exact (u.lTensor B) (d.lTensor B) := by
  intro x
  constructor
  · intro hx
    obtain ⟨L, hL, hfin⟩ := exists_finite_submodule_left_of_setFinite
      ({x} : Set (B ⊗[R] M)) (Set.finite_singleton x)
    let _ := hL
    obtain ⟨a, ha⟩ := hfin (Set.mem_singleton x)
    have ha0 : d.lTensor L a = 0 := by
      apply Module.Flat.rTensor_preserves_injective_linearMap L.subtype L.subtype_injective
      rw [map_zero, ← differential_naturality, ha, hx]
    obtain ⟨b, hb⟩ := (exact_finite_coefficients u d hquot hdu L a).mp ha0
    refine ⟨L.subtype.rTensor P b, ?_⟩
    rw [differential_naturality, hb, ha]
  · rintro ⟨a, rfl⟩
    have h : (d.lTensor B).comp (u.lTensor B) = 0 := by
      rw [← LinearMap.lTensor_comp, hdu, LinearMap.lTensor_zero]
    exact LinearMap.congr_fun h a

end FLT.Mazur.TensorKernelCyclic
