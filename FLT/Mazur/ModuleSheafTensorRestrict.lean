/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ModuleSheafTensor

/-!
# Restriction and charts for the tensor of module sheaves

The comparison is constructed from the bilinear universal property and restriction
along open immersions. Trivializations are only required on a covering.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct

universe u

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

namespace FLT.Mazur.FCurve.ModuleSheafTensor

variable {X Y Z : Scheme.{u}}

/-- Restrict a bilinear pairing along an open immersion. -/
def Bilinear.restrict {M N P : X.Modules} (b : Bilinear M N P)
    (j : Y ⟶ X) [IsOpenImmersion j] :
    Bilinear (M.restrict j) (N.restrict j) (P.restrict j) where
  app U :=
    { toFun := fun m ↦
        { toFun := fun n ↦ b.app (j ''ᵁ U) m n
          map_add' := fun n n' ↦ (b.app (j ''ᵁ U) m).map_add n n'
          map_smul' := fun r n ↦ (b.app (j ''ᵁ U) m).map_smul ((j.appIso U).inv r) n }
      map_add' := fun m m' ↦ by ext n; exact congrArg (fun f ↦ f n) ((b.app (j ''ᵁ U)).map_add m m')
      map_smul' := fun r m ↦ by
        ext n
        exact congrArg (fun f ↦ f n) ((b.app (j ''ᵁ U)).map_smul ((j.appIso U).inv r) m) }
  naturality i m n := b.naturality (j.opensFunctor.map i) m n

/-- The canonical comparison from the tensor of restrictions. -/
def restrictComparison (M N : X.Modules) (j : Y ⟶ X) [IsOpenImmersion j] :
    tensor (M.restrict j) (N.restrict j) ⟶ (tensor M N).restrict j :=
  lift ((pairing M N).restrict j)

/-- The comparison carries pure tensors to their images under section restriction. -/
@[simp]
lemma restrictComparison_pure (M N : X.Modules) (j : Y ⟶ X) [IsOpenImmersion j]
    (U : Y.Opens) (m : Γ(M.restrict j, U)) (n : Γ(N.restrict j, U)) :
    ((tensor M N).restrictAppIso j U).hom
      ((restrictComparison M N j).app U (pure (M.restrict j) (N.restrict j) U m n)) =
    pure M N (j ''ᵁ U) ((M.restrictAppIso j U).hom m)
      ((N.restrictAppIso j U).hom n) := by
  rw [restrictComparison, lift_pure]
  rfl

/-- Push a bilinear pairing forward along a scheme morphism. -/
def Bilinear.pushforward {M N P : Y.Modules} (b : Bilinear M N P) (j : Y ⟶ X) :
    Bilinear ((Scheme.Modules.pushforward j).obj M)
      ((Scheme.Modules.pushforward j).obj N) ((Scheme.Modules.pushforward j).obj P) where
  app U :=
    { toFun := fun m ↦
        { toFun := fun n ↦ b.app (j ⁻¹ᵁ U) m n
          map_add' := fun n n' ↦ (b.app (j ⁻¹ᵁ U) m).map_add n n'
          map_smul' := fun r n ↦ (b.app (j ⁻¹ᵁ U) m).map_smul (j.app U r) n }
      map_add' := fun m m' ↦ by
        ext n
        exact congrArg (fun f ↦ f n) ((b.app (j ⁻¹ᵁ U)).map_add m m')
      map_smul' := fun r m ↦ by
        ext n
        exact congrArg (fun f ↦ f n) ((b.app (j ⁻¹ᵁ U)).map_smul (j.app U r) m) }
  naturality i m n := b.naturality ((TopologicalSpace.Opens.map j.base).map i) m n

/-- Precompose a bilinear pairing with two module morphisms. -/
def Bilinear.precomp {M N M' N' P : X.Modules} (b : Bilinear M' N' P)
    (f : M ⟶ M') (g : N ⟶ N') : Bilinear M N P where
  app U := ((b.app U).compl₂ (g.val.app (.op U)).hom).comp (f.val.app (.op U)).hom
  naturality i m n := by
    change b.app _ (f.app _ (M.presheaf.map i.op m))
      (g.app _ (N.presheaf.map i.op n)) = _
    have hf := ConcreteCategory.congr_hom (f.mapPresheaf.naturality i.op) m
    have hg := ConcreteCategory.congr_hom (g.mapPresheaf.naturality i.op) n
    change f.app _ (M.presheaf.map i.op m) = M'.presheaf.map i.op (f.app _ m) at hf
    change g.app _ (N.presheaf.map i.op n) = N'.presheaf.map i.op (g.app _ n) at hg
    rw [hf, hg]
    exact b.naturality i _ _

/-- The inverse comparison obtained by adjunction from the restricted pairing. -/
def restrictComparisonInv (M N : X.Modules) (j : Y ⟶ X) [IsOpenImmersion j] :
    (tensor M N).restrict j ⟶ tensor (M.restrict j) (N.restrict j) :=
  (Scheme.Modules.restrictAdjunction j).homEquiv _ _ |>.symm <|
    lift (((pairing (M.restrict j) (N.restrict j)).pushforward j).precomp
      ((Scheme.Modules.restrictAdjunction j).unit.app M)
      ((Scheme.Modules.restrictAdjunction j).unit.app N))

/-- Evaluation of the inverse comparison on a pure section of the ambient tensor. -/
lemma restrictComparisonInv_pure (M N : X.Modules) (j : Y ⟶ X) [IsOpenImmersion j]
    (U : Y.Opens) (m : Γ(M, j ''ᵁ U)) (n : Γ(N, j ''ᵁ U)) :
    (restrictComparisonInv M N j).app U
      (((tensor M N).restrictAppIso j U).inv (pure M N (j ''ᵁ U) m n)) =
    pure (M.restrict j) (N.restrict j) U
      ((M.restrictAppIso j U).inv m) ((N.restrictAppIso j U).inv n) := by
  let b := (((pairing (M.restrict j) (N.restrict j)).pushforward j).precomp
    ((Scheme.Modules.restrictAdjunction j).unit.app M)
    ((Scheme.Modules.restrictAdjunction j).unit.app N))
  rw [restrictComparisonInv, Adjunction.homEquiv_counit]
  change (tensor (M.restrict j) (N.restrict j)).presheaf.map
    (eqToHom (j.preimage_image_eq U).symm).op
    ((lift b).app (j ''ᵁ U) (pure M N (j ''ᵁ U) m n)) = _
  erw [lift_pure]
  change (tensor (M.restrict j) (N.restrict j)).presheaf.map _
    (pure (M.restrict j) (N.restrict j) _
      (M.presheaf.map (homOfLE (j.image_preimage_le (j ''ᵁ U))).op m)
      (N.presheaf.map (homOfLE (j.image_preimage_le (j ''ᵁ U))).op n)) = _
  rw [pure_restrict]
  change pure (M.restrict j) (N.restrict j) U
    (M.presheaf.map _ (M.presheaf.map _ m))
    (N.presheaf.map _ (N.presheaf.map _ n)) = _
  have cancel (P : X.Modules) {V W : X.Opens} (a : V ⟶ W) (c : W ⟶ V)
      (x : Γ(P, V)) : P.presheaf.map a.op (P.presheaf.map c.op x) = x := by
    change (P.presheaf.map c.op ≫ P.presheaf.map a.op) x = x
    rw [← Functor.map_comp, show c.op ≫ a.op = 𝟙 _ from Subsingleton.elim _ _,
      CategoryTheory.Functor.map_id]
    rfl
  erw [cancel, cancel]
  rfl

/-- Local pure sections determine maps out of a restricted tensor. -/
lemma restrict_hom_ext {M N : X.Modules} (j : Y ⟶ X) [IsOpenImmersion j]
    {P : Y.Modules} {f g : (tensor M N).restrict j ⟶ P}
    (h : ∀ U m n, f.app U (((tensor M N).restrictAppIso j U).inv
      (pure M N (j ''ᵁ U) m n)) = g.app U
        (((tensor M N).restrictAppIso j U).inv (pure M N (j ''ᵁ U) m n))) : f = g := by
  apply ((Scheme.Modules.restrictAdjunction j).homEquiv _ _).injective
  apply hom_ext
  intro U m n
  change f.app (j ⁻¹ᵁ U) ((tensor M N).presheaf.map
    (homOfLE (j.image_preimage_le U)).op (pure M N U m n)) =
    g.app (j ⁻¹ᵁ U) ((tensor M N).presheaf.map
      (homOfLE (j.image_preimage_le U)).op (pure M N U m n))
  rw [pure_restrict]
  exact h _ _ _

/-- Tensor products of sheaves commute with restriction along open immersions. -/
def restrictIso (M N : X.Modules) (j : Y ⟶ X) [IsOpenImmersion j] :
    (tensor M N).restrict j ≅ tensor (M.restrict j) (N.restrict j) where
  hom := restrictComparisonInv M N j
  inv := restrictComparison M N j
  hom_inv_id := by
    apply restrict_hom_ext j
    intro U m n
    change (restrictComparison M N j).app U
      ((restrictComparisonInv M N j).app U _) = _
    rw [restrictComparisonInv_pure]
    exact restrictComparison_pure M N j U m n
  inv_hom_id := by
    apply hom_ext
    intro U m n
    change (restrictComparisonInv M N j).app U
      ((restrictComparison M N j).app U _) = _
    have h := restrictComparison_pure M N j U m n
    change (restrictComparison M N j).app U _ = _ at h
    rw [h]
    exact restrictComparisonInv_pure M N j U m n

/-- The forward restriction isomorphism on pure sections. -/
@[simp]
lemma restrictIso_hom_pure (M N : X.Modules) (j : Y ⟶ X) [IsOpenImmersion j]
    (U : Y.Opens) (m : Γ(M, j ''ᵁ U)) (n : Γ(N, j ''ᵁ U)) :
    (restrictIso M N j).hom.app U
      (((tensor M N).restrictAppIso j U).inv (pure M N (j ''ᵁ U) m n)) =
    pure (M.restrict j) (N.restrict j) U
      ((M.restrictAppIso j U).inv m) ((N.restrictAppIso j U).inv n) :=
  restrictComparisonInv_pure M N j U m n

/-- Restriction along the identity agrees with the identity restriction comparison. -/
lemma restrictIso_id (M N : X.Modules) :
    (restrictIso M N (𝟙 X)).hom ≫
      map (Scheme.Modules.restrictFunctorId.hom.app M)
        (Scheme.Modules.restrictFunctorId.hom.app N) =
    Scheme.Modules.restrictFunctorId.hom.app (tensor M N) := by
  apply restrict_hom_ext (𝟙 X)
  intro U m n
  change (map _ _).app U ((restrictIso M N (𝟙 X)).hom.app U _) = _
  rw [restrictIso_hom_pure, map_pure]
  simp only [Scheme.Modules.restrictFunctorId_hom_app_app]
  exact (pure_restrict M N _ m n).symm

set_option maxHeartbeats 800000 in
-- Two nested restrictions require extra elaboration steps for scalar transports.
/-- Restriction along a composite agrees with two successive restrictions. -/
lemma restrictIso_comp (M N : X.Modules) (j : Y ⟶ X) (k : Z ⟶ Y)
    [IsOpenImmersion j] [IsOpenImmersion k] :
    (Scheme.Modules.restrictFunctorComp k j).hom.app (tensor M N) ≫
      (Scheme.Modules.restrictFunctor k).map (restrictIso M N j).hom ≫
      (restrictIso (M.restrict j) (N.restrict j) k).hom =
    (restrictIso M N (k ≫ j)).hom ≫
      map ((Scheme.Modules.restrictFunctorComp k j).hom.app M)
        ((Scheme.Modules.restrictFunctorComp k j).hom.app N) := by
  apply restrict_hom_ext (k ≫ j)
  intro U m n
  simp only [Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply,
    restrictIso_hom_pure, Scheme.Modules.restrictFunctorComp_hom_app_app]
  change (restrictIso (M.restrict j) (N.restrict j) k).hom.app U
    ((restrictIso M N j).hom.app (k ''ᵁ U)
      ((tensor M N).presheaf.map _ (pure M N ((k ≫ j) ''ᵁ U) m n))) = _
  erw [pure_restrict]
  erw [restrictIso_hom_pure, restrictIso_hom_pure, map_pure]
  rfl

/-- An isomorphism of module sheaves induces a linear equivalence on sections. -/
def sectionsCongr {M N : X.Modules} (e : M ≅ N) (U : X.Opens) :
    Γ(M, U) ≃ₗ[Γ(X, U)] Γ(N, U) :=
  ((SheafOfModules.evaluation X.ringCatSheaf (.op U)).mapIso e).toLinearEquiv

@[simp]
lemma sectionsCongr_apply {M N : X.Modules} (e : M ≅ N) (U : X.Opens) (m : Γ(M, U)) :
    sectionsCongr e U m = e.hom.app U m := rfl

/-- The tensor trivialization specified by two trivializations. -/
def trivialTensorIso {M N : X.Modules}
    (e : M ≅ SheafOfModules.unit X.ringCatSheaf)
    (f : N ≅ SheafOfModules.unit X.ringCatSheaf) :
    tensor M N ≅ SheafOfModules.unit X.ringCatSheaf :=
  congr e f ≪≫ leftUnitor _

/-- Tensor trivializations multiply the two scalar coordinates. -/
@[simp]
lemma trivialTensorIso_pure {M N : X.Modules}
    (e : M ≅ SheafOfModules.unit X.ringCatSheaf)
    (f : N ≅ SheafOfModules.unit X.ringCatSheaf)
    (U : X.Opens) (m : Γ(M, U)) (n : Γ(N, U)) :
    (trivialTensorIso e f).hom.app U (pure M N U m n) =
      (show Γ(X, U) from e.hom.app U m) * (show Γ(X, U) from f.hom.app U n) := by
  change (leftUnitor _).hom.app U ((map e.hom f.hom).app U _) = _
  rw [map_pure, leftUnitor_pure]
  rfl

/-- On a trivializing chart, tensoring sections agrees with sections of the tensor. -/
def trivialSectionsEquiv {M N : X.Modules}
    (e : M ≅ SheafOfModules.unit X.ringCatSheaf)
    (f : N ≅ SheafOfModules.unit X.ringCatSheaf) (U : X.Opens) :
    Γ(M, U) ⊗[Γ(X, U)] Γ(N, U) ≃ₗ[Γ(X, U)] Γ(tensor M N, U) :=
  (TensorProduct.congr (sectionsCongr e U) (sectionsCongr f U)).trans
    ((TensorProduct.lid Γ(X, U) Γ(X, U)).trans (sectionsCongr (trivialTensorIso e f) U).symm)

/-- The chart section comparison is the canonical pure-section map. -/
@[simp]
lemma trivialSectionsEquiv_tmul {M N : X.Modules}
    (e : M ≅ SheafOfModules.unit X.ringCatSheaf)
    (f : N ≅ SheafOfModules.unit X.ringCatSheaf)
    (U : X.Opens) (m : Γ(M, U)) (n : Γ(N, U)) :
    trivialSectionsEquiv e f U (m ⊗ₜ n) = pure M N U m n := by
  apply (sectionsCongr (trivialTensorIso e f) U).injective
  rw [trivialSectionsEquiv, LinearEquiv.trans_apply, LinearEquiv.trans_apply]
  erw [LinearEquiv.apply_symm_apply, sectionsCongr_apply, trivialTensorIso_pure]
  rfl

/-- The chart section comparison does not depend on the chosen trivializations. -/
lemma trivialSectionsEquiv_eq {M N : X.Modules}
    (e e' : M ≅ SheafOfModules.unit X.ringCatSheaf)
    (f f' : N ≅ SheafOfModules.unit X.ringCatSheaf) (U : X.Opens) :
    trivialSectionsEquiv e f U = trivialSectionsEquiv e' f' U := by
  apply LinearEquiv.toLinearMap_injective
  ext m n
  exact (trivialSectionsEquiv_tmul e f U m n).trans
    (trivialSectionsEquiv_tmul e' f' U m n).symm

/-- The tensor trivialization on a common open chart. -/
def chartIso {M N : X.Modules} (j : Y ⟶ X) [IsOpenImmersion j]
    (e : M.restrict j ≅ SheafOfModules.unit Y.ringCatSheaf)
    (f : N.restrict j ≅ SheafOfModules.unit Y.ringCatSheaf) :
    (tensor M N).restrict j ≅ SheafOfModules.unit Y.ringCatSheaf :=
  restrictIso M N j ≪≫ trivialTensorIso e f

/-- The coordinate of a pure section on a chart is the product of its coordinates. -/
lemma chartIso_pure {M N : X.Modules} (j : Y ⟶ X) [IsOpenImmersion j]
    (e : M.restrict j ≅ SheafOfModules.unit Y.ringCatSheaf)
    (f : N.restrict j ≅ SheafOfModules.unit Y.ringCatSheaf)
    (U : Y.Opens) (m : Γ(M, j ''ᵁ U)) (n : Γ(N, j ''ᵁ U)) :
    (chartIso j e f).hom.app U
      (((tensor M N).restrictAppIso j U).inv (pure M N (j ''ᵁ U) m n)) =
    (show Γ(Y, U) from e.hom.app U ((M.restrictAppIso j U).inv m)) *
      (show Γ(Y, U) from f.hom.app U ((N.restrictAppIso j U).inv n)) := by
  change (trivialTensorIso e f).hom.app U ((restrictIso M N j).hom.app U _) = _
  rw [restrictIso_hom_pure, trivialTensorIso_pure]

/-- Tensor sections on a chart compare canonically with the restricted ambient tensor. -/
def chartSectionsEquiv {M N : X.Modules} (j : Y ⟶ X) [IsOpenImmersion j]
    (e : M.restrict j ≅ SheafOfModules.unit Y.ringCatSheaf)
    (f : N.restrict j ≅ SheafOfModules.unit Y.ringCatSheaf) (U : Y.Opens) :
    Γ(M.restrict j, U) ⊗[Γ(Y, U)] Γ(N.restrict j, U) ≃ₗ[Γ(Y, U)]
      Γ((tensor M N).restrict j, U) :=
  (trivialSectionsEquiv e f U).trans (sectionsCongr (restrictIso M N j).symm U)

/-- The section comparison on a chart sends a simple tensor to the ambient pure section. -/
@[simp]
lemma chartSectionsEquiv_tmul {M N : X.Modules} (j : Y ⟶ X) [IsOpenImmersion j]
    (e : M.restrict j ≅ SheafOfModules.unit Y.ringCatSheaf)
    (f : N.restrict j ≅ SheafOfModules.unit Y.ringCatSheaf)
    (U : Y.Opens) (m : Γ(M.restrict j, U)) (n : Γ(N.restrict j, U)) :
    ((tensor M N).restrictAppIso j U).hom (chartSectionsEquiv j e f U (m ⊗ₜ n)) =
    pure M N (j ''ᵁ U) ((M.restrictAppIso j U).hom m)
      ((N.restrictAppIso j U).hom n) := by
  change ((tensor M N).restrictAppIso j U).hom
    ((restrictComparison M N j).app U (trivialSectionsEquiv e f U (m ⊗ₜ n))) = _
  rw [trivialSectionsEquiv_tmul]
  exact restrictComparison_pure M N j U m n

/-- A module sheaf has rank one locally if trivializing open neighborhoods cover the scheme. -/
def LocallyRankOne (M : X.Modules) : Prop :=
  ∀ x : X, ∃ U : X.Opens, x ∈ U ∧
    Nonempty (M.restrict U.ι ≅ SheafOfModules.unit U.toScheme.ringCatSheaf)

/-- A trivialization restricts to a smaller open chart. -/
def restrictTrivialization {M : X.Modules} {U V : X.Opens} (h : U ≤ V)
    (e : M.restrict V.ι ≅ SheafOfModules.unit V.toScheme.ringCatSheaf) :
    M.restrict U.ι ≅ SheafOfModules.unit U.toScheme.ringCatSheaf :=
  (Scheme.Modules.restrictFunctorCongr (X.homOfLE_ι h).symm).app M ≪≫
    (Scheme.Modules.restrictFunctorComp (X.homOfLE h) V.ι).app M ≪≫
    (Scheme.Modules.restrictFunctor (X.homOfLE h)).mapIso e ≪≫
    Scheme.Modules.restrictUnitIso _

/-- Two locally rank-one module sheaves have common trivializing neighborhoods. -/
lemma LocallyRankOne.common {M N : X.Modules} (hM : LocallyRankOne M)
    (hN : LocallyRankOne N) (x : X) :
    ∃ U : X.Opens, x ∈ U ∧
      Nonempty (M.restrict U.ι ≅ SheafOfModules.unit U.toScheme.ringCatSheaf) ∧
      Nonempty (N.restrict U.ι ≅ SheafOfModules.unit U.toScheme.ringCatSheaf) := by
  obtain ⟨U, hxU, ⟨e⟩⟩ := hM x
  obtain ⟨V, hxV, ⟨f⟩⟩ := hN x
  exact ⟨U ⊓ V, ⟨hxU, hxV⟩, ⟨restrictTrivialization inf_le_left e⟩,
    ⟨restrictTrivialization inf_le_right f⟩⟩

/-- The constructed tensor preserves local rank-one triviality. -/
lemma LocallyRankOne.tensor {M N : X.Modules} (hM : LocallyRankOne M)
    (hN : LocallyRankOne N) : LocallyRankOne (tensor M N) := by
  intro x
  obtain ⟨U, hx, ⟨e⟩, ⟨f⟩⟩ := hM.common hN x
  exact ⟨U, hx, ⟨chartIso U.ι e f⟩⟩

end FLT.Mazur.FCurve.ModuleSheafTensor
