/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Deformations.HardlyRamifiedFlatLift
public import FLT.Deformations.DeSmitLenstra.TraceSpecialization
public import FLT.Deformations.ProartinianImage

/-!
# The trace image inside the actual finite-flat HR quotient

This is the image of the unrestricted universal trace ring in the constructed
HR ring with its specified quotient row at two. Its identification with the
source's completed-tensor-product image still requires the local-ring comparison.
Neither arithmetic Noetherianity nor p-adic module finiteness is asserted.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory GaloisRepresentation
namespace Deformation
open ProartinianCat
variable (O : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O]
  [Finite (IsLocalRing.ResidueField O)]
  {p : ℕ} [Fact p.Prime] (hp : Odd p)
  [Algebra ℤ_[p] (residueField (𝓞 := O))] [Algebra ℤ_[p] O]
  [IsScalarTower ℤ_[p] O (residueField (𝓞 := O))]
  {V : Type} [AddCommGroup V] [Module (residueField (𝓞 := O)) V]
  [Module.Finite (residueField (𝓞 := O)) V] [Module.Free (residueField (𝓞 := O)) V]
  (hdim : Module.rank (residueField (𝓞 := O)) V = 2)
  (ρ : GaloisRep ℚ (residueField (𝓞 := O)) V) (hρ : IsHardlyRamified hp hdim ρ)
local notation "G" => Field.absoluteGaloisGroup ℚ
local notation "r" => hardlyTwoFramedResidual O hp hdim ρ hρ
local notation "H" => hardlyFlatObject O hp hdim ρ hρ

/-- The actual map from universal trace coefficients to the HR quotient. -/
def hardlyTraceSpecialization : universalTraceRingObject O G (Fin 2) r ⟶ H :=
  traceSpecialization O G (Fin 2) r H (hardlyFlatLift O hp hdim ρ hρ)

/-- The image as a subalgebra of the specified framed HR quotient. -/
def hardlyTraceImage : Subalgebra O H :=
  (hardlyTraceSpecialization O hp hdim ρ hρ).hom.toAlgHom.range

/-- The image is exactly the closed trace algebra of the actual HR lift. -/
theorem hardlyTraceImage_eq : hardlyTraceImage O hp hdim ρ hρ =
    (Algebra.adjoin O (Set.range fun g : G ↦
      ((hardlyFlatLift O hp hdim ρ hρ).val g).val.trace)).topologicalClosure :=
  traceSpecializationImage_eq O G (Fin 2) r H (hardlyFlatLift O hp hdim ρ hρ)

/-- This image is closed in the HR quotient. -/
theorem hardlyTraceImage_closed : IsClosed (hardlyTraceImage O hp hdim ρ hρ : Set H) :=
  traceSpecializationImage_closed O G (Fin 2) r H (hardlyFlatLift O hp hdim ρ hρ)

/-- The same image presented as a local proartinian ring with the original residue field. -/
def hardlyTraceImageObject : ProartinianCat O :=
  imageObject (hardlyTraceSpecialization O hp hdim ρ hρ)

/-- The quotient map from the unrestricted universal trace ring. -/
def hardlyTraceImageProjection :
    universalTraceRingObject O G (Fin 2) r ⟶ hardlyTraceImageObject O hp hdim ρ hρ :=
  imageProjection (hardlyTraceSpecialization O hp hdim ρ hρ)

/-- The quotient presentation agrees with the actual subalgebra image. -/
def hardlyTraceImageEquiv :
    hardlyTraceImageObject O hp hdim ρ hρ ≃ₐ[O] hardlyTraceImage O hp hdim ρ hρ :=
  imageEquivRange (hardlyTraceSpecialization O hp hdim ρ hρ)

/-- The image embeds into the framed HR quotient. -/
def hardlyTraceImageInclusion : hardlyTraceImageObject O hp hdim ρ hρ ⟶ H :=
  imageInclusion (hardlyTraceSpecialization O hp hdim ρ hρ)

/-- The embedding is injective. -/
theorem hardlyTraceImageInclusion_injective :
    Function.Injective (hardlyTraceImageInclusion O hp hdim ρ hρ).hom :=
  imageInclusion_injective (hardlyTraceSpecialization O hp hdim ρ hρ)

/-- The quotient map is surjective. -/
theorem hardlyTraceImageProjection_surjective :
    Function.Surjective (hardlyTraceImageProjection O hp hdim ρ hρ).hom :=
  imageProjection_surjective (hardlyTraceSpecialization O hp hdim ρ hρ)

/-- The factorization is through this same HR specialization. -/
theorem hardlyTraceImage_factorization :
    hardlyTraceImageProjection O hp hdim ρ hρ ≫ hardlyTraceImageInclusion O hp hdim ρ hρ =
      hardlyTraceSpecialization O hp hdim ρ hρ :=
  imageProjection_inclusion (hardlyTraceSpecialization O hp hdim ρ hρ)

/-- The residue field is identified with the original coefficient residue field. -/
def hardlyTraceImageResidueEquiv :
    IsLocalRing.ResidueField O ≃ₐ[O]
      IsLocalRing.ResidueField (hardlyTraceImageObject O hp hdim ρ hρ) :=
  IsResidueAlgebra.algEquiv O (hardlyTraceImageObject O hp hdim ρ hρ)

end Deformation
