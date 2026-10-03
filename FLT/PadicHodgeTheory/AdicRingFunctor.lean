/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import Mathlib.RingTheory.AdicCompletion.Algebra

/-! # Ring endomorphisms on ideal-adic completions -/

@[expose] public noncomputable section
namespace PadicHodgeTheory
variable {R : Type*} [CommRing R] (I : Ideal R)

/-- Preservation of an ideal implies preservation of every power. -/
theorem adicRing_pow_le (f : R →+* R) (hf : I ≤ I.comap f) (n : ℕ) :
    I ^ n ≤ (I ^ n).comap f :=
  (pow_le_pow_left' hf n).trans (Ideal.le_comap_pow f n)

/-- Inverse ideal-preserving maps preserve membership in all powers in both directions. -/
theorem adicRing_pow_mem_iff (f g : R →+* R) (hf : I ≤ I.comap f)
    (hg : I ≤ I.comap g) (hgf : ∀ x, g (f x) = x) (n : ℕ) (x : R) :
    f x ∈ I ^ n ↔ x ∈ I ^ n := by
  constructor
  · intro hx
    have h : g (f x) ∈ I ^ n := adicRing_pow_le I g hg n hx
    rwa [hgf] at h
  · exact fun hx ↦ adicRing_pow_le I f hf n hx

/-- The induced ring endomorphism on a finite adic quotient. -/
def adicRingQuotientMap (f : R →+* R) (hf : I ≤ I.comap f) (n : ℕ) :
    R ⧸ (I ^ n • ⊤ : Ideal R) →+* R ⧸ (I ^ n • ⊤ : Ideal R) :=
  Ideal.quotientMap _ f (by
    simpa only [smul_eq_mul, Ideal.mul_top] using (adicRing_pow_le I f hf n))

/-- Finite quotient functoriality commutes with transition to a smaller quotient. -/
theorem adicRingQuotientMap_transition (f : R →+* R) (hf : I ≤ I.comap f)
    {m n : ℕ} (h : m ≤ n) (x : R ⧸ (I ^ n • ⊤ : Ideal R)) :
    AdicCompletion.transitionMap I R h (adicRingQuotientMap I f hf n x) =
      adicRingQuotientMap I f hf m (AdicCompletion.transitionMap I R h x) := by
  induction x using Quotient.inductionOn' with | h x => rfl

/-- An ideal-preserving ring endomorphism acts on compatible adic coordinates. -/
def adicRingMap (f : R →+* R) (hf : I ≤ I.comap f) :
    AdicCompletion I R →+* AdicCompletion I R where
  toFun x := ⟨fun n ↦ adicRingQuotientMap I f hf n (x.val n), fun h ↦ by
    rw [adicRingQuotientMap_transition, x.property h]⟩
  map_one' := Subtype.ext (funext fun n ↦ map_one (adicRingQuotientMap I f hf n))
  map_mul' x y := Subtype.ext (funext fun n ↦ map_mul (adicRingQuotientMap I f hf n) _ _)
  map_zero' := Subtype.ext (funext fun n ↦ map_zero (adicRingQuotientMap I f hf n))
  map_add' x y := Subtype.ext (funext fun n ↦ map_add (adicRingQuotientMap I f hf n) _ _)

/-- Evaluation of the completion map is its finite quotient map. -/
@[simp] theorem adicRingMap_val (f : R →+* R) (hf : I ≤ I.comap f)
    (x : AdicCompletion I R) (n : ℕ) :
    (adicRingMap I f hf x).val n = adicRingQuotientMap I f hf n (x.val n) := rfl

/-- The induced completion map extends the given ring endomorphism. -/
@[simp] theorem adicRingMap_algebraMap (f : R →+* R) (hf : I ≤ I.comap f) (x : R) :
    adicRingMap I f hf (algebraMap R (AdicCompletion I R) x) =
      algebraMap R (AdicCompletion I R) (f x) := rfl

/-- Identity on the source induces identity on the completion. -/
theorem adicRingMap_id (h : I ≤ I.comap (RingHom.id R)) (x : AdicCompletion I R) :
    adicRingMap I (RingHom.id R) h x = x := by
  apply Subtype.ext
  funext n
  change adicRingQuotientMap I (RingHom.id R) h n (x.val n) = x.val n
  induction x.val n using Quotient.inductionOn' with | h a => rfl

/-- Composition on the source induces composition on the completion. -/
theorem adicRingMap_comp (f g : R →+* R) (hf : I ≤ I.comap f) (hg : I ≤ I.comap g)
    (hfg : I ≤ I.comap (f.comp g)) (x : AdicCompletion I R) :
    adicRingMap I (f.comp g) hfg x = adicRingMap I f hf (adicRingMap I g hg x) := by
  apply Subtype.ext
  funext n
  change adicRingQuotientMap I (f.comp g) hfg n (x.val n) =
    adicRingQuotientMap I f hf n (adicRingQuotientMap I g hg n (x.val n))
  induction x.val n using Quotient.inductionOn' with | h a => rfl

/-- Reduction modulo the defining ideal commutes with the completion map. -/
theorem adicRingMap_evalOne (f : R →+* R) (hf : I ≤ I.comap f)
    (x : AdicCompletion I R) :
    AdicCompletion.evalOneₐ I (adicRingMap I f hf x) =
      Ideal.quotientMap I f hf (AdicCompletion.evalOneₐ I x) := by
  change Ideal.Quotient.factor (show I ^ 1 ≤ I by simp)
      (Ideal.Quotient.factor (show I ^ 1 • ⊤ ≤ I ^ 1 by simp)
        (adicRingQuotientMap I f hf 1 (x.val 1))) =
    Ideal.quotientMap I f hf (Ideal.Quotient.factor (show I ^ 1 ≤ I by simp)
      (Ideal.Quotient.factor (show I ^ 1 • ⊤ ≤ I ^ 1 by simp) (x.val 1)))
  induction x.val 1 using Quotient.inductionOn' with | h a => rfl

end PadicHodgeTheory
