/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AdicCompletionAlgEquiv
public import FLT.Mazur.AdicDerivationQuotient

/-!
# Extension of original relative derivations to adic completions

The finite derivative maps form a compatible system. Their limit is an
actual relative derivation on the completed algebra, with values in the
completed original module and with the original values on original sections.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.AdicDerivationFiltration

set_option backward.isDefEq.respectTransparency false

variable {R A M : Type*} [CommRing R] [CommRing A] [Algebra R A]
  [AddCommGroup M] [Module R M] [Module A M]
  (d : Derivation R A M) (I : Ideal A)

/-- The compatible finite derivatives define a map on actual adic completions. -/
def completionMap (a : AdicCompletion I A) : AdicCompletion I M :=
  ⟨fun n ↦ quotientMap d I n (AdicCompletion.evalₐ I (n + 1) a), by
    intro m n hmn
    exact (quotientMap_transition d I hmn _).trans
      (congrArg (quotientMap d I m)
        (AdicCompletionAlgEquiv.eval_compatible (K := R) I (Nat.add_le_add_right hmn 1) a))⟩

/-- Finite evaluation of the extension is precisely the original finite derivative. -/
@[simp] theorem completionMap_eval (n : ℕ) (a : AdicCompletion I A) :
    AdicCompletion.eval I M n (completionMap d I a) =
      quotientMap d I n (AdicCompletion.evalₐ I (n + 1) a) := rfl

/-- The extension retains the original derivative on every original section. -/
@[simp] theorem completionMap_of (a : A) :
    completionMap d I (AdicCompletion.of I A a) = AdicCompletion.of I M (d a) := by
  apply Subtype.ext
  funext n
  exact congrArg (quotientMap d I n) (AdicCompletion.evalₐ_of I (n + 1) a)

/-- The completed map is additive. -/
theorem completionMap_add (a b : AdicCompletion I A) :
    completionMap d I (a + b) = completionMap d I a + completionMap d I b := by
  apply Subtype.ext
  funext n
  exact (congrArg (quotientMap d I n) (map_add (AdicCompletion.evalₐ I (n + 1)) a b)).trans
    (quotientMap_add d I n _ _)

/-- The extended map satisfies the Leibniz rule for the actual completed-module action. -/
theorem completionMap_mul (a b : AdicCompletion I A) :
    completionMap d I (a * b) = a • completionMap d I b + b • completionMap d I a := by
  apply Subtype.ext
  funext n
  change quotientMap d I n (AdicCompletion.evalₐ I (n + 1) (a * b)) =
    a.val n • (completionMap d I b).val n + b.val n • (completionMap d I a).val n
  rw [map_mul, quotientMap_mul, AdicCompletion.val_smul_eq_evalₐ_smul,
    AdicCompletion.val_smul_eq_evalₐ_smul]
  have ha : Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.le_succ n))
      (AdicCompletion.evalₐ I (n + 1) a) = AdicCompletion.evalₐ I n a :=
    AdicCompletionAlgEquiv.eval_compatible (K := R) I (Nat.le_succ n) a
  have hb : Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.le_succ n))
      (AdicCompletion.evalₐ I (n + 1) b) = AdicCompletion.evalₐ I n b :=
    AdicCompletionAlgEquiv.eval_compatible (K := R) I (Nat.le_succ n) b
  rw [ha, hb]
  rfl

variable [IsScalarTower R A M]

/-- The extension retains relative scalar linearity. -/
theorem completionMap_smul (r : R) (a : AdicCompletion I A) :
    completionMap d I (r • a) = r • completionMap d I a := by
  apply Subtype.ext
  funext n
  change quotientMap d I n (AdicCompletion.evalₐ I (n + 1) (r • a)) =
    r • quotientMap d I n (AdicCompletion.evalₐ I (n + 1) a)
  exact (congrArg (quotientMap d I n)
    (((AdicCompletion.evalₐ I (n + 1)).restrictScalars R).toLinearMap.map_smul r a)).trans
      (quotientMap_smul d I n r _)

/-- Every original relative derivation extends to the actual completed algebra and module. -/
def completion : Derivation R (AdicCompletion I A) (AdicCompletion I M) where
  toFun := completionMap d I
  map_add' := completionMap_add d I
  map_smul' := completionMap_smul d I
  map_one_eq_zero' := by
    change completionMap d I (AdicCompletion.of I A 1) = 0
    rw [completionMap_of, d.map_one_eq_zero, map_zero]
  leibniz' := completionMap_mul d I

/-- The actual completed derivation extends the original one on original sections. -/
@[simp] theorem completion_of (a : A) :
    completion d I (AdicCompletion.of I A a) = AdicCompletion.of I M (d a) :=
  completionMap_of d I a

end FLT.Mazur.AdicDerivationFiltration
