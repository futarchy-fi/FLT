/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.LocalModelIdentification
public import FLT.GroupScheme.RaynaudScalarAction

/-!
# Scalar actions on the specified local integral model

Small ramification extends the actual coefficient action on the given model.
Generic faithfulness proves the action laws and compatibility with integral
maps whose generic maps are linear. No replacement by a maximal model is used.
-/

@[expose] public noncomputable section
namespace ThreeAdicPlan
open NumberField IsLocalRing

variable {K k : Type} [Field K] [NumberField K] [Field k]
  (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
  [IsAdicComplete (maximalIdeal (v.adicCompletionIntegers K)) (v.adicCompletionIntegers K)]
  (p : ℕ) [Fact p.Prime] [CharP k p]
  [CharP (ResidueField (v.adicCompletionIntegers K)) p]
  (X : FF (v.adicCompletionIntegers K) (v.adicCompletion K)) [Module k X.Points]
  [SMulCommClass k (AlgebraicClosure (v.adicCompletion K) ≃ₐ[v.adicCompletion K]
    AlgebraicClosure (v.adicCompletion K)) X.Points]
  (he : RaynaudParameters.order (p : v.adicCompletionIntegers K) < p - 1)

include he in
/-- The coefficient action extends on the original integral model with all ring laws. -/
theorem exists_local_integral_scalars :
    ∃ lift : k → ModelHom X X,
      (∀ a x, genericHom (lift a) x = a • x) ∧
      lift 0 = ModelHom.zero X X ∧
      lift 1 = BialgHom.id (v.adicCompletionIntegers K) X.CoordinateRing ∧
      (∀ a b, lift (a + b) = (lift a).add (lift b)) ∧
      (∀ a b, lift (a * b) = (lift b).comp (lift a)) := by
  let idX : GenericGaloisHom X X :=
    { toFun := id, map_zero' := rfl, map_add' := fun _ _ ↦ rfl, map_smul' := fun _ _ ↦ rfl }
  apply exists_integral_scalar_action idX Function.bijective_id
  let : Module (ZMod p) X.Points := AddCommGroup.zmodModule (fun x ↦ by
    rw [← Nat.cast_smul_eq_nsmul (R := k), CharP.cast_eq_zero, zero_smul])
  exact fun g ↦ (extend_from_local_prime_field v p he g).exists

/-- The specified integral scalar map. -/
def localIntegralScalar (a : k) : ModelHom X X :=
  (exists_local_integral_scalars v p X he).choose a

/-- It induces the original coefficient action. -/
@[simp] theorem localIntegralScalar_generic (a : k) (x : X.Points) :
    genericHom (localIntegralScalar v p X he a) x = a • x :=
  (exists_local_integral_scalars v p X he).choose_spec.1 a x

/-- Generic linearity forces commutation with the actual integral scalar lifts. -/
theorem localIntegralScalar_natural
    (Y : FF (v.adicCompletionIntegers K) (v.adicCompletion K)) [Module k Y.Points]
    [SMulCommClass k (AlgebraicClosure (v.adicCompletion K) ≃ₐ[v.adicCompletion K]
      AlgebraicClosure (v.adicCompletion K)) Y.Points]
    (f : ModelHom X Y) (hf : ∀ (a : k) x, genericHom f (a • x) = a • genericHom f x)
    (a : k) :
    (localIntegralScalar v p X he a).comp f = f.comp (localIntegralScalar v p Y he a) := by
  apply genericHom_injective X Y
  ext x
  simp only [genericHom_comp, localIntegralScalar_generic, hf]

end ThreeAdicPlan
