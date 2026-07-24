import Mathlib.CategoryTheory.Category.KleisliCat

open CategoryTheory

universe up

variable (M : Type up → Type up) [Monad M] [LawfulMonad M]

def kleisliΦ : Type up ⥤ KleisliCat M where
  obj X := X
  map f := fun x => pure (f x)
  map_id X := by
    ext x
    rfl
  map_comp f g := by
    ext x
    dsimp [CategoryStruct.comp, KleisliCat.comp_def, Bind.kleisliRight]
    simp [pure_bind]
