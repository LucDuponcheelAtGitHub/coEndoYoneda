import CoEndoYoneda
import Mathlib.CategoryTheory.Category.KleisliCat

open CategoryTheory
open CoEndoYoneda
open FunctionalCategory

universe u
variable (S : Type u)

instance testInst : FunctionalCategory (KleisliCat (StateM S)) where
  Φ := statefulΦ S

  γμ := {
    app := fun X => fun (f : PUnit.{u+1} → StateM S (PUnit.{u+1} → StateM S X)) => f PUnit.unit
    naturality := fun X Y f => by grind
  }
  γη := {
    app := fun X => fun (x : X) => pure (fun _ : PUnit.{u+1} => pure x)
    naturality := fun X Y f => by grind
  }

  γ_left_unit := fun X => by
    ext f s
    dsimp [CategoryStruct.comp, CategoryStruct.id, KleisliCat.comp_def, KleisliCat.id_def, bind, pure, StateT.bind, StateT.pure, StateT.run]
    rfl

  φ := fun f => fun x => pure (f x)
  φ_eq := fun f => by rfl
  γη_φ := fun X => by
    ext f s
    dsimp [CategoryStruct.comp, CategoryStruct.id, KleisliCat.comp_def, KleisliCat.id_def, bind, pure, StateT.bind, StateT.pure, StateT.run, statefulΦ, φ, TypeCat.ofHom, ConcreteCategory.hom]
    rfl
