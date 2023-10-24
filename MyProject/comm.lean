inductive my_nat where
| zero : my_nat
| succ : my_nat → my_nat

-- Slight rewrite of the my_add function to make it work with Lean4 syntax

def my_add (m : my_nat) (n : my_nat) : my_nat :=
  match n with
  | (my_nat.zero) => m
  | (my_nat.succ n') => my_nat.succ (my_add m n')

theorem my_add_comm : ∀ (m n : my_nat), my_add m n = my_add n m := by
  intro m n
  revert m
  induction n
  -- we do the above so we can perform induction on the second arugment, while keeping the first argument quantified
  case zero =>
    intro m
    induction m
    case zero =>
      simp
    case succ m' ih_m =>
      -- using left arrow inside of simp tactic, just tries to apply right hand side of the equality first
      simp [my_add, ←ih_m]
  case succ n' ih_n =>
    intro m
    induction m
    case zero =>
      have t := ih_n my_nat.zero
      simp [my_add] at t
      simp [my_add]
      exact t
    case succ m' ih_m =>
      simp [my_add]
      have t := ih_n (my_nat.succ m')
      simp [← ih_m, t, my_add]
      have t' := ih_n m'
      simp [← t']

      



