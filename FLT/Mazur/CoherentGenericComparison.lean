/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineStalkExtension
public import FLT.Mazur.CoherentComparisonLocus

/-!
# Coherent comparisons near a prescribed stalk

On a locally Noetherian scheme, canonical affine presentations turn stalk maps
into maps of localized finite modules. Their principal-open realizations give
local coherent comparisons, at any point and hence at every generic point.

`CoherentStalkNeighborhood` records the open immersion, the comparison between
actual restrictions, and its equality with the prescribed germ. Shrinking
preserves that equality. For a stalk isomorphism, the error support is closed
and strictly smaller than any support bound containing the point; on the final
neighborhood both error sheaves vanish.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite

universe u

namespace FLT.Mazur.FCurve.CoherentDevissage

variable {X Y Z : Scheme.{u}}

/-- The structure stalk acts on the actual additive module stalk. -/
instance schemeStalkModule (M : X.Modules) (x : X) :
    Module (X.presheaf.stalk x) (M.presheaf.stalk x) :=
  inferInstanceAs (Module (X.presheaf.stalk x) ↑(TopCat.Presheaf.stalk M.val.presheaf x))

/-- Scalars and module elements can be represented on a common neighborhood. -/
lemma comparison_common_germs (M : X.Modules) (x : X)
    (r : X.presheaf.stalk x) (m : M.presheaf.stalk x) :
    ∃ (U : X.Opens) (hx : x ∈ U) (a : Γ(X, U)) (n : Γ(M, U)),
      X.presheaf.germ U x hx a = r ∧ M.presheaf.germ U x hx n = m := by
  obtain ⟨U, hx, a, rfl⟩ := X.presheaf.exists_germ_eq r
  obtain ⟨V, hVU, hv, n, rfl⟩ := M.presheaf.exists_le_germ_eq m hx
  exact ⟨V, hv, X.presheaf.map (homOfLE hVU).op a, n,
    X.presheaf.germ_res_apply (homOfLE hVU) x hv a, rfl⟩

/-- Sheaf morphisms induce structure-stalk-linear maps. -/
def comparisonStalkLinear {M N : X.Modules} (f : M ⟶ N) (x : X) :
    M.presheaf.stalk x →ₗ[X.presheaf.stalk x] N.presheaf.stalk x where
  __ := ((stalk x).map f).hom
  map_smul' r m := by
    obtain ⟨U, hx, a, n, rfl, rfl⟩ := comparison_common_germs M x r m
    erw [← M.val.germ_smul]
    change (stalk x).map f (M.presheaf.germ U x hx (a • n)) =
      HSMul.hSMul (α := X.presheaf.stalk x) (β := N.presheaf.stalk x)
        (γ := N.presheaf.stalk x) (X.presheaf.germ U x hx a)
        ((stalk x).map f (M.presheaf.germ U x hx n))
    have hg (v : Γ(M, U)) : (stalk x).map f (M.presheaf.germ U x hx v) =
        N.presheaf.germ U x hx (f.app U v) :=
      TopCat.Presheaf.stalkFunctor_map_germ_apply U x hx f.mapPresheaf v
    rw [hg, hg, Scheme.Modules.Hom.app_smul]
    exact N.val.germ_smul x U hx a (f.app U n)

/-- A sheaf isomorphism gives a linear equivalence on its stalks. -/
def comparisonStalkEquiv {M N : X.Modules} (e : M ≅ N) (x : X) :
    M.presheaf.stalk x ≃ₗ[X.presheaf.stalk x] N.presheaf.stalk x :=
  LinearEquiv.ofBijective (comparisonStalkLinear e.hom x)
    (ConcreteCategory.bijective_of_isIso ((stalk x).map e.hom))

/-- Additive coordinates for restriction along an open immersion. -/
def comparisonRestrictStalk (j : Y ⟶ X) [IsOpenImmersion j] (y : Y) (M : X.Modules) :
    (M.restrict j).presheaf.stalk y ≃+ M.presheaf.stalk (j y) :=
  ((Scheme.Modules.restrictStalkNatIso j y).app M).addCommGroupIsoToAddEquiv

/-- Restriction coordinates preserve germs on image opens. -/
lemma comparisonRestrictStalk_germ (j : Y ⟶ X) [IsOpenImmersion j] (y : Y)
    (M : X.Modules) (U : Y.Opens) (hy : y ∈ U) (m : Γ(M.restrict j, U)) :
    comparisonRestrictStalk j y M ((M.restrict j).presheaf.germ U y hy m) =
      M.presheaf.germ (j ''ᵁ U) (j y) (by simpa) m :=
  congrArg (fun f ↦ f m) (Scheme.Modules.germ_restrictStalkNatIso_hom_app j y M hy)

/-- The inverse structure-stalk map sends a scalar germ to its image-open germ. -/
lemma comparisonRestrictScalar_germ (j : Y ⟶ X) [IsOpenImmersion j] (y : Y)
    (U : Y.Opens) (hy : y ∈ U) (r : Γ(Y, U)) :
    inv (j.stalkMap y) (Y.presheaf.germ U y hy r) =
      X.presheaf.germ (j ''ᵁ U) (j y) (by simpa) ((j.appIso U).inv r) := by
  apply (ConcreteCategory.bijective_of_isIso (j.stalkMap y)).injective
  rw [← ConcreteCategory.comp_apply (inv (j.stalkMap y)), IsIso.inv_hom_id]
  simp only [CommRingCat.id_apply, Scheme.Hom.germ_stalkMap_apply]
  have h := congrArg (fun f ↦ f r) (j.appIso_inv_app U)
  change j.app (j ''ᵁ U) ((j.appIso U).inv r) = _ at h
  rw [h]
  exact (Y.presheaf.germ_res_apply (eqToHom (j.preimage_image_eq U)) y (by simpa) r).symm

/-- Restriction coordinates respect the inverse structure-stalk map. -/
lemma comparisonRestrictStalk_smul (j : Y ⟶ X) [IsOpenImmersion j] (y : Y)
    (M : X.Modules) (r : Y.presheaf.stalk y) (m : (M.restrict j).presheaf.stalk y) :
    comparisonRestrictStalk j y M (r • m) =
      inv (j.stalkMap y) r • comparisonRestrictStalk j y M m := by
  obtain ⟨U, hy, a, n, rfl, rfl⟩ := comparison_common_germs (M.restrict j) y r m
  erw [← (M.restrict j).val.germ_smul, comparisonRestrictStalk_germ,
    comparisonRestrictStalk_germ, comparisonRestrictScalar_germ]
  exact M.val.germ_smul (j y) (j ''ᵁ U) (by simpa) ((j.appIso U).inv a) n

/-- Transport a prescribed linear map to an open-immersion restriction. -/
def comparisonRestrictedLinear (j : Y ⟶ X) [IsOpenImmersion j] (y : Y)
    {M N : X.Modules}
    (f : M.presheaf.stalk (j y) →ₗ[X.presheaf.stalk (j y)] N.presheaf.stalk (j y)) :
    (M.restrict j).presheaf.stalk y →ₗ[Y.presheaf.stalk y]
      (N.restrict j).presheaf.stalk y where
  __ := (comparisonRestrictStalk j y N).symm.toAddMonoidHom.comp
    (f.toAddMonoidHom.comp (comparisonRestrictStalk j y M).toAddMonoidHom)
  map_smul' r m := by
    apply (comparisonRestrictStalk j y N).injective
    change comparisonRestrictStalk j y N
      ((comparisonRestrictStalk j y N).symm (f (comparisonRestrictStalk j y M (r • m)))) =
      comparisonRestrictStalk j y N
        (r • (comparisonRestrictStalk j y N).symm (f (comparisonRestrictStalk j y M m)))
    rw [AddEquiv.apply_symm_apply, comparisonRestrictStalk_smul,
      comparisonRestrictStalk_smul, AddEquiv.apply_symm_apply, map_smul]

/-- Restriction coordinates are natural in sheaf morphisms. -/
lemma comparisonRestrictStalk_naturality (j : Y ⟶ X) [IsOpenImmersion j] (y : Y)
    {M N : X.Modules} (f : M ⟶ N) (m : (M.restrict j).presheaf.stalk y) :
    comparisonRestrictStalk j y N
      ((stalk y).map ((Scheme.Modules.restrictFunctor j).map f) m) =
      (stalk (j y)).map f (comparisonRestrictStalk j y M m) :=
  congrArg (fun f ↦ f m) ((Scheme.Modules.restrictStalkNatIso j y).hom.naturality f)

/-- A coherent affine stalk map extends through the canonical section presentations. -/
theorem exists_affine_coherent_stalk_extension {R : CommRingCat.{u}} [IsNoetherianRing R]
    (M N : (Spec R).Modules) [M.IsFinitePresentation] [N.IsFinitePresentation]
    (x : Spec R) (f : M.presheaf.stalk x →ₗ[(Spec R).presheaf.stalk x] N.presheaf.stalk x) :
    ∃ (U : (Spec R).Opens) (hx : x ∈ U) (g : M.restrict U.ι ⟶ N.restrict U.ι),
      ∀ m, comparisonRestrictStalk U.ι ⟨x, hx⟩ N ((stalk (X := U.toScheme) ⟨x, hx⟩).map g m) =
        f (comparisonRestrictStalk U.ι ⟨x, hx⟩ M m) := by
  let eM := affineCoherentIso M
  let eN := affineCoherentIso N
  let aM := comparisonStalkEquiv eM x
  let aN := comparisonStalkEquiv eN x
  have : Module.Finite R (moduleSpecΓFunctor.obj M) := affineCoherent_finite_sections M
  have := Module.finitePresentation_of_finite R (moduleSpecΓFunctor.obj M)
  let f' := aN.toLinearMap.comp (f.comp aM.symm.toLinearMap)
  obtain ⟨s, hs, g, hg⟩ := exists_principal_stalk_extension_linear x f'
  let U := affinePrincipalOpen s
  let F := Scheme.Modules.restrictFunctor U.ι
  refine ⟨U, hs, F.map eM.hom ≫ g ≫ F.map eN.inv, ?_⟩
  intro m
  simp only [Functor.map_comp, ConcreteCategory.comp_apply]
  rw [comparisonRestrictStalk_naturality]
  change (stalk x).map eN.inv
    (affineRestrictStalkEquiv U ⟨x, hs⟩ _
      ((stalk (X := U.toScheme) ⟨x, hs⟩).map g
        ((stalk (X := U.toScheme) ⟨x, hs⟩).map (F.map eM.hom) m))) = _
  rw [hg]
  change (stalk x).map eN.inv
    (aN (f (aM.symm (comparisonRestrictStalk U.ι ⟨x, hs⟩ _
      ((stalk (X := U.toScheme) ⟨x, hs⟩).map (F.map eM.hom) m))))) = _
  rw [comparisonRestrictStalk_naturality]
  change (stalk x).map eN.inv
    (aN (f (aM.symm (aM (comparisonRestrictStalk U.ι ⟨x, hs⟩ M m))))) = _
  rw [LinearEquiv.symm_apply_apply]
  exact congrArg (fun h ↦ h (f (comparisonRestrictStalk U.ι ⟨x, hs⟩ M m)))
    ((stalk x).mapIso eN).hom_inv_id

/-- Stalk coordinates commute with successive restrictions. -/
lemma comparisonRestrictStalk_comp (j : Y ⟶ X) (k : Z ⟶ Y)
    [IsOpenImmersion j] [IsOpenImmersion k] (z : Z) (M : X.Modules)
    (m : (M.restrict (k ≫ j)).presheaf.stalk z) :
    comparisonRestrictStalk (k ≫ j) z M m =
      comparisonRestrictStalk j (k z) M (comparisonRestrictStalk k z (M.restrict j)
        ((stalk z).map ((Scheme.Modules.restrictFunctorComp k j).hom.app M) m)) := by
  obtain ⟨U, hz, m, rfl⟩ := (M.restrict (k ≫ j)).presheaf.exists_germ_eq m
  have hg := TopCat.Presheaf.stalkFunctor_map_germ_apply U z hz
    ((Scheme.Modules.restrictFunctorComp k j).hom.app M).mapPresheaf m
  change (stalk z).map ((Scheme.Modules.restrictFunctorComp k j).hom.app M)
    ((M.restrict (k ≫ j)).presheaf.germ U z hz m) =
      ((M.restrict j).restrict k).presheaf.germ U z hz
        (((Scheme.Modules.restrictFunctorComp k j).hom.app M).app U m) at hg
  erw [hg, comparisonRestrictStalk_germ, comparisonRestrictStalk_germ,
    comparisonRestrictStalk_germ, Scheme.Modules.restrictFunctorComp_hom_app_app]
  exact (M.presheaf.germ_res_apply (eqToHom (by simp)) (j (k z)) (by simpa) m).symm

/-- Restriction coordinates with an explicit identification of the ambient point. -/
def comparisonStalkAt (j : Y ⟶ X) [IsOpenImmersion j] (y : Y) (x : X)
    (h : j y = x) (M : X.Modules) : (M.restrict j).presheaf.stalk y ≃+ M.presheaf.stalk x :=
  (comparisonRestrictStalk j y M).trans
    (eqToIso (congrArg (fun z ↦ M.presheaf.stalk z) h)).addCommGroupIsoToAddEquiv

/-- A genuine open neighborhood carrying a map with exactly the prescribed stalk. -/
structure CoherentStalkNeighborhood (M N : X.Modules) (x : X)
    (f : M.presheaf.stalk x →ₗ[X.presheaf.stalk x] N.presheaf.stalk x) where
  /-- The scheme forming the neighborhood. -/
  scheme : Scheme.{u}
  /-- The open immersion into the original scheme. -/
  inclusion : scheme ⟶ X
  isOpenImmersion : IsOpenImmersion inclusion
  /-- The point of the neighborhood lying above the prescribed point. -/
  point : scheme
  point_eq : inclusion point = x
  /-- The comparison between the actual restrictions of the two sheaves. -/
  map : M.restrict inclusion ⟶ N.restrict inclusion
  germ : ∀ m, comparisonStalkAt inclusion point x point_eq N ((stalk point).map map m) =
    f (comparisonStalkAt inclusion point x point_eq M m)

attribute [instance] CoherentStalkNeighborhood.isOpenImmersion

/-- Every coherent stalk map extends to an open neighborhood, in particular at generic points. -/
theorem exists_coherent_stalk_neighborhood [IsLocallyNoetherian X]
    (M N : X.Modules) [M.IsFinitePresentation] [N.IsFinitePresentation]
    (x : X) (f : M.presheaf.stalk x →ₗ[X.presheaf.stalk x] N.presheaf.stalk x) :
    Nonempty (CoherentStalkNeighborhood M N x f) := by
  obtain ⟨i, y, rfl⟩ := X.affineOpenCover.openCover.exists_eq x
  let j : Spec (X.affineOpenCover.X i) ⟶ X := X.affineOpenCover.f i
  have := coherentPresentation_restrict j M
  have := coherentPresentation_restrict j N
  have : IsNoetherianRing (X.affineOpenCover.X i) :=
    (isLocallyNoetherian_Spec).mp (isLocallyNoetherian_of_isOpenImmersion j)
  obtain ⟨U, hy, g, hg⟩ := exists_affine_coherent_stalk_extension
    (M.restrict j) (N.restrict j) y (comparisonRestrictedLinear j y f)
  let eM := (Scheme.Modules.restrictFunctorComp U.ι j).app M
  let eN := (Scheme.Modules.restrictFunctorComp U.ι j).app N
  refine ⟨⟨U.toScheme, U.ι ≫ j, inferInstance, ⟨y, hy⟩, rfl,
    eM.hom ≫ g ≫ eN.inv, ?_⟩⟩
  intro m
  change comparisonRestrictStalk (U.ι ≫ j) ⟨y, hy⟩ N
    ((stalk (X := U.toScheme) ⟨y, hy⟩).map (eM.hom ≫ g ≫ eN.inv) m) =
    f (comparisonRestrictStalk (U.ι ≫ j) ⟨y, hy⟩ M m)
  rw [comparisonRestrictStalk_comp, comparisonRestrictStalk_comp]
  simp only [Functor.map_comp, ConcreteCategory.comp_apply]
  have he := congrArg (fun h ↦ h
    ((stalk (X := U.toScheme) ⟨y, hy⟩).map g
      ((stalk (X := U.toScheme) ⟨y, hy⟩).map eM.hom m)))
    ((stalk (X := U.toScheme) ⟨y, hy⟩).mapIso eN).inv_hom_id
  change (stalk (X := U.toScheme) ⟨y, hy⟩).map eN.hom
    ((stalk (X := U.toScheme) ⟨y, hy⟩).map eN.inv _) = _ at he
  erw [he, hg]
  exact (comparisonRestrictStalk j y N).apply_symm_apply _

/-- Point identifications are compatible with composition of restrictions. -/
lemma comparisonStalkAt_comp (j : Y ⟶ X) (k : Z ⟶ Y)
    [IsOpenImmersion j] [IsOpenImmersion k] (z : Z) (x : X) (h : j (k z) = x)
    (M : X.Modules) (m : (M.restrict (k ≫ j)).presheaf.stalk z) :
    comparisonStalkAt (k ≫ j) z x h M m = comparisonStalkAt j (k z) x h M
      (comparisonRestrictStalk k z (M.restrict j)
        ((stalk z).map ((Scheme.Modules.restrictFunctorComp k j).hom.app M) m)) :=
  congrArg (eqToIso (congrArg (fun z ↦ M.presheaf.stalk z) h)).hom
    (comparisonRestrictStalk_comp j k z M m)

namespace CoherentStalkNeighborhood

variable {M N : X.Modules} {x : X}
  {f : M.presheaf.stalk x →ₗ[X.presheaf.stalk x] N.presheaf.stalk x}

/-- Shrinking a comparison preserves its exact prescribed germ. -/
def restrict (C : CoherentStalkNeighborhood M N x f) (U : C.scheme.Opens)
    (hx : C.point ∈ U) : CoherentStalkNeighborhood M N x f := by
  let eM := (Scheme.Modules.restrictFunctorComp U.ι C.inclusion).app M
  let eN := (Scheme.Modules.restrictFunctorComp U.ι C.inclusion).app N
  let g := (Scheme.Modules.restrictFunctor U.ι).map C.map
  refine ⟨U.toScheme, U.ι ≫ C.inclusion, inferInstance, ⟨C.point, hx⟩, C.point_eq,
    eM.hom ≫ g ≫ eN.inv, ?_⟩
  intro m
  rw [comparisonStalkAt_comp, comparisonStalkAt_comp]
  simp only [Functor.map_comp, ConcreteCategory.comp_apply]
  have he := congrArg (fun h ↦ h
    ((stalk (X := U.toScheme) ⟨C.point, hx⟩).map g
      ((stalk (X := U.toScheme) ⟨C.point, hx⟩).map eM.hom m)))
    ((stalk (X := U.toScheme) ⟨C.point, hx⟩).mapIso eN).inv_hom_id
  change (stalk (X := U.toScheme) ⟨C.point, hx⟩).map eN.hom
    ((stalk (X := U.toScheme) ⟨C.point, hx⟩).map eN.inv _) = _ at he
  erw [he, comparisonRestrictStalk_naturality]
  exact C.germ _

/-- An invertible restricted comparison remains invertible after transport. -/
instance restrict_map_isIso (C : CoherentStalkNeighborhood M N x f)
    (U : C.scheme.Opens) (hx : C.point ∈ U)
    [IsIso ((Scheme.Modules.restrictFunctor U.ι).map C.map)] :
    IsIso (C.restrict U hx).map := by
  dsimp [restrict]
  infer_instance

/-- The stalk of an extension of a linear equivalence is invertible. -/
lemma isIso_stalk {e : M.presheaf.stalk x ≃ₗ[X.presheaf.stalk x] N.presheaf.stalk x}
    (C : CoherentStalkNeighborhood M N x e.toLinearMap) : IsIso ((stalk C.point).map C.map) := by
  apply (ConcreteCategory.isIso_iff_bijective _).mpr
  let a := comparisonStalkAt C.inclusion C.point x C.point_eq M
  let b := comparisonStalkAt C.inclusion C.point x C.point_eq N
  constructor
  · intro m n h
    apply a.injective
    apply e.injective
    exact (C.germ m).symm.trans ((congrArg b h).trans (C.germ n))
  · intro n
    refine ⟨a.symm (e.symm (b n)), ?_⟩
    apply b.injective
    exact (C.germ _).trans
      ((congrArg e (a.apply_symm_apply _)).trans (e.apply_symm_apply _))

/-- The error support is closed and strictly smaller than every bound containing the point. -/
theorem error_support [IsLocallyNoetherian X]
    [M.IsFinitePresentation] [N.IsFinitePresentation]
    {e : M.presheaf.stalk x ≃ₗ[X.presheaf.stalk x] N.presheaf.stalk x}
    (C : CoherentStalkNeighborhood M N x e.toLinearMap)
    (T : Set C.scheme) (hx : C.point ∈ T)
    (hM : support (M.restrict C.inclusion) ⊆ T)
    (hN : support (N.restrict C.inclusion) ⊆ T) :
    IsClosed (support (kernel C.map) ∪ support (cokernel C.map)) ∧
      support (kernel C.map) ∪ support (cokernel C.map) ⊂ T := by
  have := isLocallyNoetherian_of_isOpenImmersion C.inclusion
  have := coherentPresentation_restrict C.inclusion M
  have := coherentPresentation_restrict C.inclusion N
  have := C.isIso_stalk
  exact comparison_error_support_ssubset C.map C.point T hx hM hN

end CoherentStalkNeighborhood

/-- A coherent stalk isomorphism extends to a neighborhood isomorphism with zero error sheaves. -/
theorem exists_coherent_comparison_neighborhood [IsLocallyNoetherian X]
    (M N : X.Modules) [M.IsFinitePresentation] [N.IsFinitePresentation] (x : X)
    (e : M.presheaf.stalk x ≃ₗ[X.presheaf.stalk x] N.presheaf.stalk x) :
    ∃ C : CoherentStalkNeighborhood M N x e.toLinearMap,
      IsIso C.map ∧ IsZero (kernel C.map) ∧ IsZero (cokernel C.map) := by
  obtain ⟨C⟩ := exists_coherent_stalk_neighborhood M N x e.toLinearMap
  have := isLocallyNoetherian_of_isOpenImmersion C.inclusion
  have := coherentPresentation_restrict C.inclusion M
  have := coherentPresentation_restrict C.inclusion N
  have := C.isIso_stalk
  obtain ⟨U, hx, _, hi, _, _⟩ := exists_comparison_neighborhood C.map C.point ⊤ trivial
  have := hi
  exact ⟨C.restrict U hx, inferInstance, isZero_kernel_of_mono _, isZero_cokernel_of_epi _⟩

end FLT.Mazur.FCurve.CoherentDevissage
