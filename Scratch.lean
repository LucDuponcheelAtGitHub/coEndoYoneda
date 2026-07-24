import Mathlib.CategoryTheory.Category.KleisliCat
import CoEndoYoneda

open CategoryTheory
open CoEndoYoneda
open FunctionalCategory

universe u
variable (S : Type u)

def statefulΦ : Type u ⥤ KleisliCat (StateM S) where
  obj X := X
  map f := fun x => pure (f x)
  map_id X := by rfl
  map_comp f g := by rfl

instance : FunctionalCategory (KleisliCat (StateM S)) where
  Φ := statefulΦ S

  γμ := {
    app := fun X => fun (f : PUnit.{u+1} → StateM S (PUnit.{u+1} → StateM S X)) => f PUnit.unit
    naturality := fun X Y f => by sorry
  }
  γη := {
    app := fun X => fun (x : X) => pure (fun _ : PUnit.{u+1} => pure x)
    naturality := fun X Y f => by sorry
  }

  γ_left_unit := fun X => by
    ext x s
    rfl

  φ := fun f => fun x => pure (f x)
  φ_eq := fun f => by rfl
  γη_φ := fun X => by sorry
