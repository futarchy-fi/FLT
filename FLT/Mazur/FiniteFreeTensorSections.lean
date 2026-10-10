/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ProjectiveTwistTensorInverse

/-!
# Finite coordinates for sections of a free tensor

Every section of a finite free sheaf tensored with a module sheaf is a finite
sum of pure generator tensors. This holds over every open, without an affine
hypothesis, using the actual finite coproduct comparison.
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry Scheme.Modules

namespace FLT.Mazur.FCurve.ModuleSheafTensor

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

attribute [local instance] HasBiproduct.of_hasCoproduct

variable {X : Scheme} (N : X.Modules) (I : Type) [Fintype I]

/-- Every section of a finite coproduct is a sum of its actual summand inclusions. -/
theorem finiteCoproductSection_sum (U : X.Opens) (s : Γ(∐ (fun _ : I ↦ N), U)) :
    ∃ t : I → Γ(N, U), s = ∑ i, (Sigma.ι (fun _ : I ↦ N) i).app U (t i) := by
  let e := biproduct.isoCoproduct (fun _ : I ↦ N)
  let z := e.inv.app U s
  refine ⟨fun i ↦ (biproduct.π (fun _ : I ↦ N) i).app U z, ?_⟩
  have hsum (S : Finset I) :
      (∑ i ∈ S, biproduct.π (fun _ : I ↦ N) i ≫ Sigma.ι (fun _ : I ↦ N) i).app U z =
        ∑ i ∈ S, (Sigma.ι (fun _ : I ↦ N) i).app U
          ((biproduct.π (fun _ : I ↦ N) i).app U z) := by
    classical
    induction S using Finset.induction_on with
    | empty => simp
    | @insert i S hi ih => simp [hi, Hom.add_app, Hom.comp_app, ih]
  have he := congrArg (fun f ↦ f.app U z)
    (biproduct.desc_eq (g := Sigma.ι (fun _ : I ↦ N)))
  rw [← biproduct.isoCoproduct_hom] at he
  change e.hom.app U (e.inv.app U s) = _ at he
  rw [← ConcreteCategory.comp_apply, ← Hom.comp_app, Iso.inv_hom_id] at he
  exact he.trans (hsum Finset.univ)

/-- Sections of a finite free tensor are sums of pure tensors with the original generators. -/
theorem freeTensorSection_sum (U : X.Opens)
    (s : Γ(tensor (SheafOfModules.free I) N, U)) :
    ∃ t : I → Γ(N, U), s = ∑ i,
      pure (SheafOfModules.free I) N U
        ((SheafOfModules.ιFree (R := X.ringCatSheaf) i).val.app (.op U) (1 : Γ(X, U))) (t i) := by
  obtain ⟨t, ht⟩ := finiteCoproductSection_sum N I U ((freeTensorIso N I).hom.app U s)
  refine ⟨t, ?_⟩
  apply (ConcreteCategory.bijective_of_isIso ((freeTensorIso N I).hom.app U)).1
  rw [map_sum]
  simpa only [freeTensorIso_pure_generator, one_smul] using ht

end FLT.Mazur.FCurve.ModuleSheafTensor
