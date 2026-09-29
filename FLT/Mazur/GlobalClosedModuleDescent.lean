/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ClosedDescentGluingMaps

/-!
# Global closed module descent

Compatible families of the actual quotient charts construct the descended
module sheaf. The ambient comparisons glue to recover the original sheaf.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
open AlgebraicGeometry.Scheme.Modules
open FLT.Mazur.ModuleSheafMorphismGluing

universe u

namespace FLT.Mazur.FCurve.CoherentDevissage.GlobalClosedModuleDescent

open ClosedDescentCharts

variable {Y : Scheme.{u}}

/-- Compatible comparisons on subopens induce compatible slice-site morphisms. -/
lemma compatible_of_subopens {A B : Y.Modules}
    (c : ∀ (U : Y.affineOpens) (V : Y.Opens), V ≤ U.1 →
      (A.restrict V.ι ⟶ B.restrict V.ι))
    (hn : ∀ (U : Y.affineOpens) (V : Y.Opens) (h : V ≤ U.1),
      (restrictFunctor (Y.homOfLE h)).map (c U U.1 le_rfl) ≫
          (nestedRestriction h).hom.app B =
        (nestedRestriction h).hom.app A ≫ c U V h)
    (he : ∀ (U U' : Y.affineOpens) (V : Y.Opens) (h : V ≤ U.1) (h' : V ≤ U'.1),
      c U V h = c U' V h') :
    Compatible (fun U : Y.affineOpens ↦ U.1)
      (fun U ↦ sliceMap U.1 (c U U.1 le_rfl)) := by
  intro U U' V h h'
  have hi := sliceMap_nested (P := A) (Q := B) h
    (c U U.1 le_rfl) (c U V h) (hn U V h) V le_rfl
  have hj := sliceMap_nested (P := A) (Q := B) h'
    (c U' U'.1 le_rfl) (c U' V h') (hn U' V h') V le_rfl
  rw [he U U' V h h'] at hi
  exact hi.trans hj.symm

/-- Invertibility of module morphisms can be checked on the affine open cover. -/
lemma isIso_of_affine_restrict {A B : Y.Modules} (f : A ⟶ B)
    (hf : ∀ U : Y.affineOpens, IsIso ((restrictFunctor U.1.ι).map f)) : IsIso f := by
  let F := SheafOfModules.toSheaf Y.ringCatSheaf
  have hs : IsIso (F.map f) := by
    apply TopCat.Sheaf.isIso_iff_isIso_basis (B := fun U : Y.affineOpens ↦ U.1)
      (by simpa only [Subtype.range_coe_subtype, Set.ofPred_mem_eq] using Y.isBasis_affineOpens)
    intro U
    have ha := Hom.isIso_iff_isIso_app.mp (hf U) (U.1.ι ⁻¹ᵁ U.1)
    change IsIso (f.app (U.1.ι ''ᵁ (U.1.ι ⁻¹ᵁ U.1))) at ha
    have he : U.1.ι ''ᵁ (U.1.ι ⁻¹ᵁ U.1) = U.1 := by
      rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι, inf_idem]
    rw [he] at ha
    exact ha
  apply Hom.isIso_iff_isIso_app.mpr
  intro V
  exact inferInstanceAs (IsIso ((F.map f).hom.app (op V)))

variable (I : Y.IdealSheafData) (M : Y.Modules)
    [M.IsFinitePresentation] (hM : IdealKilled I M)

/-- The global module sheaf consists of compatible quotient-chart sections. -/
def descent : I.subscheme.Modules := (gluingData I M hM).glued

/-- The constructed descent restricts to its original quotient charts. -/
def chartIso (U : Y.affineOpens) :
    (descent I M hM).restrict (I.subschemeι ⁻¹ᵁ U.1).ι ≅ chart I M hM U :=
  (gluingData I M hM).restrictionIso U

/-- The projection maps obey the lifted transition on every ambient subopen. -/
lemma projection_transitionOn (U U' : Y.affineOpens) (V : Y.Opens)
    (h : V ≤ U.1) (h' : V ≤ U'.1) :
    (restrictFunctor (I.subschemeι ⁻¹ᵁ V).ι).map ((gluingData I M hM).projection U) ≫
        (transitionOn I M hM U U' V h h').hom =
      (restrictFunctor (I.subschemeι ⁻¹ᵁ V).ι).map ((gluingData I M hM).projection U') := by
  apply (Function.LeftInverse.injective (sliceMap_restrictionEquiv (I.subschemeι ⁻¹ᵁ V)))
  rw [sliceMap_comp, sliceMap_over, sliceMap_over]
  apply SheafOfModules.hom_ext
  ext S s
  have ht := s.property U U' S.unop.left le_rfl
    ((leOfHom S.unop.hom).trans (I.subschemeι.preimage_mono h))
    ((leOfHom S.unop.hom).trans (I.subschemeι.preimage_mono h'))
  change localApp (overlap I M hM U U').hom _
    (res (chartExtension I M hM U) le_rfl (s.val U)) =
      res (chartExtension I M hM U') le_rfl (s.val U') at ht
  simp only [res_self] at ht
  rw [overlap_on_subopen I M hM U U' V h h' S.unop.left (leOfHom S.unop.hom)] at ht
  change localApp (sliceMap (I.subschemeι ⁻¹ᵁ V)
    (transitionOn I M hM U U' V h h').hom) (leOfHom S.unop.hom) (s.val U) = s.val U'
  exact ht

/-- A projected chart compares with the ambient sheaf on any smaller open. -/
def comparisonMapOn (U : Y.affineOpens) (V : Y.Opens) (h : V ≤ U.1) :
    ((pushforward I.subschemeι).obj (descent I M hM)).restrict V.ι ⟶ M.restrict V.ι :=
  (restrictFunctor V.ι).map
    ((pushforward I.subschemeι).map ((gluingData I M hM).projection U)) ≫
      (subopenComparison I M hM U V h).hom

/-- Base change expresses the comparison by the restricted closed projection. -/
lemma comparisonMapOn_eq (U : Y.affineOpens) (V : Y.Opens) (h : V ≤ U.1) :
    comparisonMapOn I M hM U V h =
      (closedPushforwardRestriction I.subschemeι V).hom.app (descent I M hM) ≫
        (pushforward (I.subschemeι ∣_ V)).map
          ((restrictFunctor (I.subschemeι ⁻¹ᵁ V).ι).map
            ((gluingData I M hM).projection U)) ≫
        (comparisonOn I M hM U V h).hom := by
  exact (NatIso.naturality_2_assoc (closedPushforwardRestriction I.subschemeι V)
    ((gluingData I M hM).projection U) (subopenComparison I M hM U V h).hom).symm


/-- Different projected charts give the same comparison on their common subopens. -/
lemma comparisonMapOn_eq_of_le (U U' : Y.affineOpens) (V : Y.Opens)
    (h : V ≤ U.1) (h' : V ≤ U'.1) :
    comparisonMapOn I M hM U V h = comparisonMapOn I M hM U' V h' := by
  have ht := congrArg Iso.hom (transitionOn_pushforward I M hM U U' V h h')
  have hp := congrArg ((pushforward (I.subschemeι ∣_ V)).map)
    (projection_transitionOn I M hM U U' V h h')
  simp only [Functor.mapIso_hom, Iso.trans_hom, Iso.symm_hom] at ht
  rw [Functor.map_comp] at hp
  erw [ht] at hp
  have he := congrArg (fun a ↦ a ≫ (comparisonOn I M hM U' V h').hom) hp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id] at he
  simp only [comparisonMapOn_eq]
  exact congrArg (fun a ↦
    (closedPushforwardRestriction I.subschemeι V).hom.app (descent I M hM) ≫ a) he

/-- Restricting a comparison further agrees with the direct comparison. -/
lemma comparisonMapOn_nested (U : Y.affineOpens) (V W : Y.Opens)
    (h : V ≤ U.1) (k : W ≤ V) :
    (restrictFunctor (Y.homOfLE k)).map (comparisonMapOn I M hM U V h) ≫
        (nestedRestriction k).hom.app M =
      (nestedRestriction k).hom.app _ ≫ comparisonMapOn I M hM U W (k.trans h) := by
  have hn := (nestedRestriction k).hom.naturality
    ((pushforward I.subschemeι).map ((gluingData I M hM).projection U))
  have hc := congrArg Iso.hom (subopenComparison_nested I M hM U V W h k)
  simp only [Functor.comp_map] at hn
  simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom] at hc
  change (restrictFunctor (Y.homOfLE k)).map
    ((restrictFunctor V.ι).map
      ((pushforward I.subschemeι).map ((gluingData I M hM).projection U)) ≫
      (subopenComparison I M hM U V h).hom) ≫ _ = _
  rw [Functor.map_comp, Category.assoc, hc]
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun a ↦ a ≫ (subopenComparison I M hM U W (k.trans h)).hom) hn).trans
      (Category.assoc _ _ _))


/-- The comparisons on the affine cover are compatible as slice-site morphisms. -/
lemma comparison_compatible :
    Compatible (M := (pushforward I.subschemeι).obj (descent I M hM)) (N := M)
      (fun U : Y.affineOpens ↦ U.1)
      (fun U ↦ sliceMap (P := (pushforward I.subschemeι).obj (descent I M hM)) (Q := M)
        U.1 (comparisonMapOn I M hM U U.1 le_rfl)) :=
  compatible_of_subopens (A := (pushforward I.subschemeι).obj (descent I M hM)) (B := M)
    (comparisonMapOn I M hM)
    (fun U V h ↦ comparisonMapOn_nested I M hM U U.1 V le_rfl h)
    (comparisonMapOn_eq_of_le I M hM)


/-- Glue the actual affine comparison maps to a global ambient morphism. -/
def comparisonMap : (pushforward I.subschemeι).obj (descent I M hM) ⟶ M :=
  glue (fun U : Y.affineOpens ↦ U.1) (iSup_affineOpens_eq_top Y)
    (fun U ↦ sliceMap U.1 (comparisonMapOn I M hM U U.1 le_rfl))
    (comparison_compatible I M hM)

/-- The global comparison recovers each supplied affine comparison. -/
lemma comparisonMap_restrict (U : Y.affineOpens) :
    (restrictFunctor U.1.ι).map (comparisonMap I M hM) =
      comparisonMapOn I M hM U U.1 le_rfl := by
  rw [← restrictionEquiv_over]
  change restrictionEquiv U.1 ((glue _ _ _ _).over U.1) = _
  rw [glue_over, sliceMap_restrictionEquiv]

/-- The comparison on each affine chart is invertible. -/
lemma comparisonMapOn_isIso (U : Y.affineOpens) :
    IsIso (comparisonMapOn I M hM U U.1 le_rfl) := by
  rw [comparisonMapOn_eq]
  have hp := (gluingData I M hM).restrictionProjection_isIso U
  infer_instance

/-- The global comparison is invertible, as detected on the ambient affine basis. -/
instance comparisonMap_isIso : IsIso (comparisonMap I M hM) := by
  apply isIso_of_affine_restrict
  intro U
  rw [comparisonMap_restrict]
  exact comparisonMapOn_isIso I M hM U

/-- The constructed global descent pushes forward to the original module sheaf. -/
def pushforwardIso : (pushforward I.subschemeι).obj (descent I M hM) ≅ M :=
  asIso (comparisonMap I M hM)

/-- Finite quotient presentations transport to the closed charts and cover the descent. -/
lemma descent_isFinitePresentation [IsLocallyNoetherian Y] :
    (descent I M hM).IsFinitePresentation := by
  have presentations (U : Y.affineOpens) :
      ∃ P : ((descent I M hM).over (I.subschemeι ⁻¹ᵁ U.1)).Presentation, P.IsFinite := by
    have hfin := quotient_isFinitePresentation I M hM U
    have hnoeth : IsNoetherianRing Γ(Y, U.1) :=
      IsLocallyNoetherian.component_noetherian U
    obtain ⟨P, hP⟩ := affineCoherent_exists_presentation (quotient I M hM U)
    have hp := hP
    let E := overEquiv (I.subschemeι ⁻¹ᵁ U.1)
    let e := ClosedDescentCharts.chartIso I U
    let F := restrictFunctor e.inv ⋙ E.inverse
    have hc : Limits.PreservesColimitsOfSize.{u, u} F :=
      Limits.comp_preservesColimits _ _
    let eu : SheafOfModules.unit _ ≅ F.obj (SheafOfModules.unit _) :=
      E.unitIso.app _ ≪≫ E.inverse.mapIso (restrictUnitIso e.inv).symm
    let em : F.obj (quotient I M hM U) ≅ (descent I M hM).over (I.subschemeι ⁻¹ᵁ U.1) :=
      E.inverse.mapIso ((pushforwardIsoRestrictInverse e).symm.app _ ≪≫
        (chartIso I M hM U).symm ≪≫
        (overFunctorEquiv _).symm.app (descent I M hM)) ≪≫ E.unitIso.symm.app _
    have hf := affinePresentation_map_isFinite P F eu
    exact ⟨(P.map F eu).ofIsIso em.hom, inferInstance⟩
  choose P hP using presentations
  let q : (descent I M hM).QuasicoherentData :=
    { I := Y.affineOpens
      X := fun U ↦ I.subschemeι ⁻¹ᵁ U.1
      coversTop := by
        rw [Opens.coversTop_iff, TopologicalSpace.IsOpenCover]
        exact gluingData_cover I
      presentation := P }
  refine { exists_quasicoherentData := ?_ }
  exact ⟨q, { isFinite_presentation := hP }⟩

/-- Annihilation is equivalent to membership in the closed pushforward essential image. -/
theorem killed_iff_mem_essImage :
    IdealKilled I M ↔ (pushforward I.subschemeι).essImage M := by
  constructor
  · intro h
    exact ⟨descent I M h, ⟨pushforwardIso I M h⟩⟩
  · exact idealKilled_of_mem_essImage I M

/-- The coherent essential image consists exactly of coherent ideal-killed modules. -/
theorem coherent_essentialImage [IsLocallyNoetherian Y] (P : Y.Modules) :
    (P.IsFinitePresentation ∧ IdealKilled I P) ↔
      ∃ N : I.subscheme.Modules,
        N.IsFinitePresentation ∧ Nonempty ((pushforward I.subschemeι).obj N ≅ P) := by
  constructor
  · rintro ⟨hP, hk⟩
    have hp := hP
    exact ⟨descent I P hk, descent_isFinitePresentation I P hk, ⟨pushforwardIso I P hk⟩⟩
  · rintro ⟨N, hN, ⟨e⟩⟩
    have hn := hN
    exact ⟨(SheafOfModules.isFinitePresentation Y.ringCatSheaf).prop_of_iso e
      (closedPushforward_isFinitePresentation I.subschemeι N),
      (idealKilled_subschemePushforward I N).of_iso e⟩

/-- Full faithfulness gives the unique comparison with any other descent. -/
theorem unique_descent (N : I.subscheme.Modules)
    (e : (pushforward I.subschemeι).obj N ≅ M) :
    ∃! d : descent I M hM ≅ N,
      (pushforward I.subschemeι).mapIso d = pushforwardIso I M hM ≪≫ e.symm :=
  closedPushforward_iso_unique I.subschemeι _

variable {M} {N P : Y.Modules} [N.IsFinitePresentation] [P.IsFinitePresentation]

/-- Lift every ambient morphism through the constructed global comparisons. -/
def map (hN : IdealKilled I N) (a : M ⟶ N) : descent I M hM ⟶ descent I N hN :=
  (pushforward I.subschemeι).preimage
    ((pushforwardIso I M hM).hom ≫ a ≫ (pushforwardIso I N hN).inv)

/-- The descended morphism recovers the original ambient map. -/
lemma map_pushforward (hN : IdealKilled I N) (a : M ⟶ N) :
    (pushforward I.subschemeι).map (map I hM hN a) =
      (pushforwardIso I M hM).hom ≫ a ≫ (pushforwardIso I N hN).inv :=
  Functor.map_preimage _ _

/-- The global comparisons are natural in the ambient sheaf. -/
lemma map_naturality (hN : IdealKilled I N) (a : M ⟶ N) :
    (pushforward I.subschemeι).map (map I hM hN a) ≫ (pushforwardIso I N hN).hom =
      (pushforwardIso I M hM).hom ≫ a := by
  simp only [map_pushforward, Category.assoc, Iso.inv_hom_id, Category.comp_id]

@[simp]
lemma map_id : map I hM hM (𝟙 M) = 𝟙 (descent I M hM) := by
  apply (pushforward I.subschemeι).map_injective
  simp [map_pushforward]

@[simp]
lemma map_comp (hN : IdealKilled I N) (hP : IdealKilled I P) (a : M ⟶ N) (b : N ⟶ P) :
    map I hM hP (a ≫ b) = map I hM hN a ≫ map I hN hP b := by
  apply (pushforward I.subschemeι).map_injective
  simp [map_pushforward]

/-- The full subcategory of coherent modules annihilated by the ideal. -/
def coherentKilled : ObjectProperty Y.Modules :=
  fun Q ↦ Q.IsFinitePresentation ∧ IdealKilled I Q

/-- Global closed descent is functorial on its coherent essential image. -/
def descentFunctor : (coherentKilled I).FullSubcategory ⥤ I.subscheme.Modules where
  obj Q := @descent _ I Q.obj Q.property.1 Q.property.2
  map {Q R} a := @map _ I Q.obj Q.property.1 Q.property.2 R.obj R.property.1
    R.property.2 a.hom
  map_id Q := @map_id _ I Q.obj Q.property.1 Q.property.2
  map_comp {Q R S} a b := @map_comp _ I Q.obj Q.property.1 Q.property.2
    R.obj S.obj R.property.1 S.property.1 R.property.2 S.property.2 a.hom b.hom

/-- The functorial descent recovers the inclusion of the coherent ideal-killed subcategory. -/
def descentComparison :
    descentFunctor I ⋙ pushforward I.subschemeι ≅ (coherentKilled I).ι :=
  NatIso.ofComponents (fun Q ↦ @pushforwardIso _ I Q.obj Q.property.1 Q.property.2)
    (fun {Q R} a ↦ @map_naturality _ I Q.obj Q.property.1 Q.property.2
      R.obj R.property.1 R.property.2 a.hom)

/-- Every value of the descent functor is coherent in the locally Noetherian context. -/
lemma descentFunctor_isFinitePresentation [IsLocallyNoetherian Y]
    (Q : (coherentKilled I).FullSubcategory) :
    ((descentFunctor I).obj Q).IsFinitePresentation :=
  @descent_isFinitePresentation _ I Q.obj Q.property.1 Q.property.2 _

end FLT.Mazur.FCurve.CoherentDevissage.GlobalClosedModuleDescent
