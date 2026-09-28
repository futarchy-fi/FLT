/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ScalarCohomology

/-!
# Scalar cohomology with module coefficients

For a sheaf of modules on a scheme, use the Ext-based cohomology of its underlying
abelian sheaf. Global sections act through multiplication on the coefficient sheaf.
Restriction along a structure morphism gives field scalars, functorially in the
coefficient module, and recovers the structure-sheaf construction of FC07.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite

universe u

namespace FLT.Mazur.FCurve

local instance moduleHasExt (X : Scheme.{u}) :
    HasExt.{u + 1} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) :=
  HasExt.standard _

variable {X : Scheme.{u}}

/-- Sections carry the module action of the structure sheaf on the same open. -/
instance moduleSectionsModule (M : X.Modules) (U : (Opens X)ᵒᵖ) :
    Module (X.presheaf.obj U) (M.val.obj U) :=
  (M.val.obj U).isModule

/-- A module sheaf with only its additive structure retained. -/
abbrev moduleAbelianSheaf (M : X.Modules) :
    Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} :=
  (SheafOfModules.toSheaf X.ringCatSheaf).obj M

/-- Ext-based cohomology with module coefficients. -/
def ModuleH (M : X.Modules) (n : ℕ) : Type (u + 1) :=
  Sheaf.H (moduleAbelianSheaf M) n

instance moduleHAddCommGroup (M : X.Modules) (n : ℕ) : AddCommGroup (ModuleH M n) :=
  inferInstanceAs (AddCommGroup (Sheaf.H (moduleAbelianSheaf M) n))

/-- Multiplication by the restrictions of a global section. -/
def moduleMultiply (M : X.Modules) (r : Γ(X, ⊤)) :
    moduleAbelianSheaf M ⟶ moduleAbelianSheaf M where
  hom :=
    { app := fun U ↦ AddCommGrpCat.ofHom
        { toFun := fun (x : M.val.obj U) ↦
            X.presheaf.map (homOfLE (show U.unop ≤ ⊤ from le_top)).op r • x
          map_zero' := smul_zero _
          map_add' := smul_add _ }
      naturality := by
        intro U V i
        ext x
        change M.val.obj U at x
        symm
        change M.val.map i
            (X.presheaf.map (homOfLE (show U.unop ≤ ⊤ from le_top)).op r • x) =
          X.presheaf.map (homOfLE (show V.unop ≤ ⊤ from le_top)).op r •
            (show M.val.obj V from M.val.map i x)
        rw [M.val.map_smul]
        congr 1
        exact congr($((X.presheaf.map_comp (homOfLE le_top).op i).symm) r) }

@[simp]
lemma moduleMultiply_one (M : X.Modules) : moduleMultiply M 1 = 𝟙 _ := by
  ext U x
  change M.val.obj U at x
  change X.presheaf.map (homOfLE (show U.unop ≤ ⊤ from le_top)).op 1 • x = x
  simp

@[simp]
lemma moduleMultiply_add (M : X.Modules) (r s : Γ(X, ⊤)) :
    moduleMultiply M (r + s) = moduleMultiply M r + moduleMultiply M s := by
  ext U x
  change M.val.obj U at x
  change X.presheaf.map (homOfLE (show U.unop ≤ ⊤ from le_top)).op (r + s) • x =
    X.presheaf.map (homOfLE (show U.unop ≤ ⊤ from le_top)).op r • x +
      X.presheaf.map (homOfLE (show U.unop ≤ ⊤ from le_top)).op s • x
  simp [add_smul]

lemma moduleMultiply_mul (M : X.Modules) (r s : Γ(X, ⊤)) :
    moduleMultiply M (r * s) = moduleMultiply M s ≫ moduleMultiply M r := by
  ext U x
  change M.val.obj U at x
  change X.presheaf.map (homOfLE (show U.unop ≤ ⊤ from le_top)).op (r * s) • x =
    X.presheaf.map (homOfLE (show U.unop ≤ ⊤ from le_top)).op r •
      (X.presheaf.map (homOfLE (show U.unop ≤ ⊤ from le_top)).op s • x)
  simp [mul_smul]

/-- Multiplication induces a ring action on cohomology. -/
def moduleHAction (M : X.Modules) (n : ℕ) :
    Γ(X, ⊤) →+* AddMonoid.End (ModuleH M n) where
  toFun r := Sheaf.H.map (moduleMultiply M r) n
  map_one' := by
    ext x
    change Sheaf.H.map (moduleMultiply M 1) n x = x
    rw [moduleMultiply_one, Sheaf.H.map_id_apply]
  map_mul' r s := by
    ext x
    change Sheaf.H.map (moduleMultiply M (r * s)) n x =
      Sheaf.H.map (moduleMultiply M r) n (Sheaf.H.map (moduleMultiply M s) n x)
    rw [moduleMultiply_mul, Sheaf.H.map_comp_apply]
  map_add' r s := by
    ext x
    exact congrArg (fun f ↦ Sheaf.H.map f n x) (moduleMultiply_add M r s) |>.trans
      (Sheaf.H.map_add_apply _ _ x)
  map_zero' := by
    ext x
    have h : moduleMultiply M 0 = 0 := by
      ext U y
      change M.val.obj U at y
      change X.presheaf.map (homOfLE (show U.unop ≤ ⊤ from le_top)).op 0 • y = 0
      simp
    change Sheaf.H.map (moduleMultiply M 0) n x = 0
    simp [h, Sheaf.H.map]

/-- The global-section action on cohomology is induced on the coefficient sheaf. -/
instance moduleHModule (M : X.Modules) (n : ℕ) : Module Γ(X, ⊤) (ModuleH M n) :=
  Module.compHom (ModuleH M n) (moduleHAction M n)

/-- Degree-zero cohomology agrees with the genuine global sections, linearly. -/
def moduleH0Equiv (M : X.Modules) : ModuleH M 0 ≃ₗ[Γ(X, ⊤)] M.val.obj (op ⊤) where
  toAddEquiv := Sheaf.H.equiv₀ (moduleAbelianSheaf M) isTerminalTop
  map_smul' r x := by
    change Sheaf.H.equiv₀ (moduleAbelianSheaf M) isTerminalTop
        (Sheaf.H.map (moduleMultiply M r) 0 x) = _
    rw [← Sheaf.H.equiv₀_naturality isTerminalTop (moduleMultiply M r)]
    let y : M.val.obj (op ⊤) := Sheaf.H.equiv₀ (moduleAbelianSheaf M) isTerminalTop x
    change X.presheaf.map (𝟙 (op ⊤)) r • y = r • y
    simp

/-- Multiplication commutes with every morphism of module sheaves. -/
lemma moduleMultiply_naturality {M N : X.Modules} (g : M ⟶ N) (r : Γ(X, ⊤)) :
    moduleMultiply M r ≫ (SheafOfModules.toSheaf X.ringCatSheaf).map g =
      (SheafOfModules.toSheaf X.ringCatSheaf).map g ≫ moduleMultiply N r := by
  ext U x
  exact (g.val.app U).hom.map_smul
    (X.presheaf.map (homOfLE (show U.unop ≤ ⊤ from le_top)).op r) x

/-- The map on cohomology induced by a module morphism is linear over global sections. -/
def moduleHMap {M N : X.Modules} (g : M ⟶ N) (n : ℕ) :
    ModuleH M n →ₗ[Γ(X, ⊤)] ModuleH N n where
  toFun := Sheaf.H.map ((SheafOfModules.toSheaf X.ringCatSheaf).map g) n
  map_add' := (Sheaf.H.map ((SheafOfModules.toSheaf X.ringCatSheaf).map g) n).map_add
  map_smul' r x := by
    change Sheaf.H.map _ n (Sheaf.H.map (moduleMultiply M r) n x) =
      Sheaf.H.map (moduleMultiply N r) n (Sheaf.H.map _ n x)
    rw [← Sheaf.H.map_comp_apply, moduleMultiply_naturality, Sheaf.H.map_comp_apply]

@[simp]
lemma moduleHMap_id (M : X.Modules) (n : ℕ) :
    moduleHMap (𝟙 M) n = LinearMap.id := by
  ext x
  change Sheaf.H.map ((SheafOfModules.toSheaf X.ringCatSheaf).map (𝟙 M)) n x = x
  rw [CategoryTheory.Functor.map_id, Sheaf.H.map_id_apply]

@[simp]
lemma moduleHMap_comp {M N P : X.Modules} (g : M ⟶ N) (h : N ⟶ P) (n : ℕ) :
    moduleHMap (g ≫ h) n = (moduleHMap h n).comp (moduleHMap g n) := by
  ext x
  change Sheaf.H.map ((SheafOfModules.toSheaf X.ringCatSheaf).map (g ≫ h)) n x = _
  rw [Functor.map_comp, Sheaf.H.map_comp_apply]
  rfl

/-- The degree-zero comparison intertwines cohomology maps and maps on global sections. -/
lemma moduleH0Equiv_naturality {M N : X.Modules} (g : M ⟶ N) (x : ModuleH M 0) :
    moduleH0Equiv N (moduleHMap g 0 x) = g.app ⊤ (moduleH0Equiv M x) :=
  (Sheaf.H.equiv₀_naturality isTerminalTop
    ((SheafOfModules.toSheaf X.ringCatSheaf).map g) x).symm

/-- On the unit module, multiplication is the multiplication used in FC07. -/
lemma moduleMultiply_unit (r : Γ(X, ⊤)) :
    moduleMultiply (structureUnitModule X) r = structureMultiply X r := rfl

section Scalars

variable {k : Type u} [Field k]

/-- Module cohomology retaining the chosen base morphism in its type. -/
def ModuleScalarH (_f : X ⟶ Spec (CommRingCat.of k)) (M : X.Modules) (n : ℕ) :
    Type (u + 1) := ModuleH M n

instance moduleScalarHAddCommGroup (f : X ⟶ Spec (CommRingCat.of k))
    (M : X.Modules) (n : ℕ) : AddCommGroup (ModuleScalarH f M n) :=
  inferInstanceAs (AddCommGroup (ModuleH M n))

/-- The field acts through the specified map to global sections. -/
instance moduleScalarHModule (f : X ⟶ Spec (CommRingCat.of k)) (M : X.Modules) (n : ℕ) :
    Module k (ModuleScalarH f M n) :=
  Module.compHom (ModuleH M n) (structureScalarMap f)

/-- The underlying additive group is the actual Ext-based sheaf cohomology. -/
def moduleScalarHAddEquiv (f : X ⟶ Spec (CommRingCat.of k)) (M : X.Modules) (n : ℕ) :
    ModuleScalarH f M n ≃+ Sheaf.H (moduleAbelianSheaf M) n := AddEquiv.refl _

/-- The scalar action is induced by multiplication on the coefficient sheaf. -/
lemma moduleScalarH_smul (f : X ⟶ Spec (CommRingCat.of k)) (M : X.Modules) (n : ℕ)
    (a : k) (x : ModuleScalarH f M n) :
    moduleScalarHAddEquiv f M n (a • x) =
      Sheaf.H.map (moduleMultiply M (structureScalarMap f a)) n
        (moduleScalarHAddEquiv f M n x) := rfl

/-- Module morphisms induce linear maps over the base field. -/
def moduleScalarHMap (f : X ⟶ Spec (CommRingCat.of k)) {M N : X.Modules}
    (g : M ⟶ N) (n : ℕ) : ModuleScalarH f M n →ₗ[k] ModuleScalarH f N n where
  toFun := moduleHMap g n
  map_add' := (moduleHMap g n).map_add
  map_smul' a x := (moduleHMap g n).map_smul (structureScalarMap f a) x

@[simp]
lemma moduleScalarHMap_id (f : X ⟶ Spec (CommRingCat.of k)) (M : X.Modules) (n : ℕ) :
    moduleScalarHMap f (𝟙 M) n = LinearMap.id := by
  ext x
  exact LinearMap.congr_fun (moduleHMap_id M n) x

@[simp]
lemma moduleScalarHMap_comp (f : X ⟶ Spec (CommRingCat.of k)) {M N P : X.Modules}
    (g : M ⟶ N) (h : N ⟶ P) (n : ℕ) :
    moduleScalarHMap f (g ≫ h) n =
      (moduleScalarHMap f h n).comp (moduleScalarHMap f g n) := by
  ext x
  exact LinearMap.congr_fun (moduleHMap_comp g h n) x

/-- Cohomology with module coefficients as a functor to vector spaces over the base. -/
def moduleScalarHFunctor (f : X ⟶ Spec (CommRingCat.of k)) (n : ℕ) :
    X.Modules ⥤ ModuleCat.{u + 1} k where
  obj M := ModuleCat.of k (ModuleScalarH f M n)
  map g := ModuleCat.ofHom (moduleScalarHMap f g n)
  map_id M := by ext x; exact LinearMap.congr_fun (moduleScalarHMap_id f M n) x
  map_comp g h := by ext x; exact LinearMap.congr_fun (moduleScalarHMap_comp f g h n) x

/-- Specializing to the unit coefficient recovers FC07's scalar cohomology linearly. -/
def moduleScalarHUnitEquiv (f : X ⟶ Spec (CommRingCat.of k)) (n : ℕ) :
    ModuleScalarH f (structureUnitModule X) n ≃ₗ[k] ScalarH f n where
  toAddEquiv := AddEquiv.refl _
  map_smul' _ _ := rfl

/-- Degree zero identifies linearly with global sections of the coefficient module. -/
def moduleScalarH0Equiv (f : X ⟶ Spec (CommRingCat.of k)) (M : X.Modules) :
    letI := Module.compHom (M.val.obj (op ⊤)) (structureScalarMap f)
    ModuleScalarH f M 0 ≃ₗ[k] M.val.obj (op ⊤) := by
  letI := Module.compHom (M.val.obj (op ⊤)) (structureScalarMap f)
  exact
    { toAddEquiv := (moduleH0Equiv M).toAddEquiv
      map_smul' := fun a x ↦ (moduleH0Equiv M).map_smul (structureScalarMap f a) x }

/-- The scalar degree-zero comparison also respects maps of coefficient sheaves. -/
lemma moduleScalarH0Equiv_naturality (f : X ⟶ Spec (CommRingCat.of k))
    {M N : X.Modules} (g : M ⟶ N) (x : ModuleScalarH f M 0) :
    moduleScalarH0Equiv f N (moduleScalarHMap f g 0 x) =
      g.app ⊤ (moduleScalarH0Equiv f M x) :=
  moduleH0Equiv_naturality g x

end Scalars

end FLT.Mazur.FCurve
