import Mathlib

universe u

-- The definition of Purity
def Purity (M : Type u → Type u) [Monad M] : Prop :=
  ∀ {X : Type u} (mx : M X), (mx >>= fun x => pure (pure x)) = pure mx

--------------------------------------------------------------------------------
-- 1. Option Monad
--------------------------------------------------------------------------------
theorem option_not_pure : ¬ Purity (Option : Type → Type) := by
  intro h
  have h1 := h (none : Option Nat)
  -- none >>= f is none
  -- pure none is some none
  have h_lhs : (none >>= fun (x : Nat) => pure (pure x : Option Nat)) = none := rfl
  have h_rhs : pure (none : Option Nat) = some none := rfl
  rw [h_lhs, h_rhs] at h1
  contradiction

--------------------------------------------------------------------------------
-- 2. List Monad
--------------------------------------------------------------------------------
theorem list_not_pure : ¬ Purity (List : Type → Type) := by
  intro h
  have h1 := h ([1, 2] : List Nat)
  -- [1, 2] >>= fun x => [[x]] is [[1], [2]]
  -- pure [1, 2] is [[1, 2]]
  have h_lhs : ([1, 2] >>= fun (x : Nat) => pure (pure x : List Nat)) = [[1], [2]] := rfl
  have h_rhs : pure ([1, 2] : List Nat) = [[1, 2]] := rfl
  rw [h_lhs, h_rhs] at h1
  contradiction

--------------------------------------------------------------------------------
-- 3. Reader Monad
--------------------------------------------------------------------------------
def MyReader (R X : Type u) := R → X

instance (R : Type u) : Monad (MyReader R) where
  pure x := fun _ => x
  bind mx f := fun r => f (mx r) r

theorem reader_purity_implies (R : Type u) :
  Purity (MyReader R) → Subsingleton R := by
  intro h
  constructor
  intro r1 r2
  have h1 := h (X := R) (fun r => r)
  have h_eval := congrFun (congrFun h1 r1) r2
  exact h_eval

--------------------------------------------------------------------------------
-- 4. Writer Monad
--------------------------------------------------------------------------------
def MyWriter (W X : Type u) := X × W

instance (W : Type u) [Mul W] [One W] : Monad (MyWriter W) where
  pure x := (x, 1)
  bind mx f :=
    let (y, w') := f mx.1
    (y, mx.2 * w')

theorem writer_purity_implies (W : Type u) [Mul W] [One W] :
  Purity (MyWriter W) → ∀ w : W, w = 1 := by
  intro h w
  -- Let mx = (x, w) where x can be anything, e.g. PUnit.unit
  have h1 := h (X := PUnit) (⟨⟩, w)
  -- LHS: (⟨⟩, w) >>= fun x => ((x, 1), 1)
  --      = (((), 1), w * 1)
  -- RHS: (((), w), 1)
  have h_eq : ((PUnit.unit, (1 : W)), w * 1) = ((PUnit.unit, w), (1 : W)) := h1
  have h_eq1 := congrArg Prod.fst h_eq
  have h_w := congrArg Prod.snd h_eq1
  exact h_w.symm

--------------------------------------------------------------------------------
-- 5. State Monad
--------------------------------------------------------------------------------
def MyState (S X : Type u) := S → X × S

instance (S : Type u) : Monad (MyState S) where
  pure x := fun s => (x, s)
  bind mx f := fun s =>
    let (x, s') := mx s
    f x s'

theorem state_purity_implies (S : Type u) :
  Purity (MyState S) → Subsingleton S := by
  intro h
  constructor
  intro s1 s2
  have h1 := h (X := S) (fun s => (s, s))
  -- LHS: fun s => let (x, s') = (s, s); pure (pure x) s'
  --      = fun s => pure (pure s) s
  --      = fun s => (pure s, s)
  --      = fun s => ((fun s' => (s, s')), s)
  -- RHS: fun s => (mx, s)
  --      = fun s => ((fun s' => (s', s')), s)
  have h_eval := congrFun h1 s1
  -- LHS at s1: ((fun s' => (s1, s')), s1)
  -- RHS at s1: ((fun s' => (s', s')), s1)
  have h_fun := congrArg Prod.fst h_eval
  -- h_fun : (fun s' => (s1, s')) = (fun s' => (s', s'))
  have h_eval2 := congrFun h_fun s2
  -- LHS at s2: (s1, s2)
  -- RHS at s2: (s2, s2)
  exact congrArg Prod.fst h_eval2

--------------------------------------------------------------------------------
-- 6. Continuation Monad
--------------------------------------------------------------------------------
def MyCont (R X : Type u) := (X → R) → R

instance (R : Type u) : Monad (MyCont R) where
  pure x := fun k => k x
  bind mx f := fun k => mx (fun x => f x k)

theorem cont_purity_implies (R : Type u) :
  Purity (MyCont R) → Subsingleton R := by
  intro h
  constructor
  intro r1 r2
  -- mx : (R → R) → R = fun k => r1
  have h1 := h (X := R) (fun _ => r1)
  -- LHS: mx >>= fun x => pure (pure x)
  --      = fun k => mx (fun x => pure (pure x) k)
  --      = fun k => (fun _ => r1) (fun x => ...)
  --      = fun k => r1
  -- RHS: pure mx
  --      = fun k => k mx
  --      = fun k => k (fun _ => r1)
  -- So (fun k => r1) = fun k => k (fun _ => r1)
  -- Evaluate at k = (fun _ => r2)
  have h_eval := congrFun h1 (fun _ => r2)
  -- LHS: r1
  -- RHS: r2
  exact h_eval
