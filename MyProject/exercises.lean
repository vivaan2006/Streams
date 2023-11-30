inductive State
| s1
| s2

def R : State → State → Prop :=
   fun s₁ s₂ => s₁ = s₂ -- was plannign on using lambda but i think its removed

def R' (T : Type) : T → T → Prop := sorry

inductive Transition : State → State → Prop
| s1_to_s2 : Transition State.s1 State.s2
| s2_to_s1 : Transition State.s2 State.s1

-- (T → T → Prop)

def is_bisimulation (R : State → State → Prop) : Prop :=
  ∀ (s₁ s₂ : State),
    R s₁ s₂ →
    (∀ (s₁' : State),
      Transition s₁ s₁' →
      ∃ (s₂' : State),
        Transition s₂ s₂' ∧ R s₁' s₂') ∧
    ∀ (s₂' : State),
      Transition s₂ s₂' →
      ∃ (s₁' : State),
        Transition s₁ s₁' ∧ R s₁' s₂'

def is_bisimulation2 (StateSpace : Type) (TransitionFunction : StateSpace → StateSpace → Prop) (R : StateSpace → StateSpace → Prop) : Prop :=
  ∀ (s₁ s₂ : StateSpace),
  R s₁ s₂ →
  sorry



#check And.intro


theorem bisimulation_proof : is_bisimulation R := by
  intro s₁ s₂ h
  apply And.intro
  case left =>
    intro s₁ h₁
    cases h₁
    case s1_to_s2 =>
      apply Exists.intro State.s2
      apply And.intro
      case left =>
        cases s₂
        case s1 =>
          exact Transition.s1_to_s2
        case s2 =>
          contradiction
      case right =>
        rfl
    case s2_to_s1 =>
      apply Exists.intro State.s1
      apply And.intro
      case left =>
        cases s₂
        case s1 =>
          contradiction
        case s2 =>
          exact Transition.s2_to_s1
      case right =>
        rfl
  case right =>
    intro s₂'' h₂
    cases h₂
    case s1_to_s2 =>
      apply Exists.intro State.s2
      apply And.intro
      case left =>
        cases s₁
        case s1 =>
          exact Transition.s1_to_s2
        case s2 =>
          contradiction
      case right =>
        rfl
    case s2_to_s1 =>
      apply Exists.intro State.s1
      apply And.intro
      case left =>
        cases s₁
        case s1 =>
          contradiction
        case s2 =>
          exact Transition.s2_to_s1
      case right =>
        rfl


theorem bisimulation_proof_two : is_bisimulation R := by
  intro s₁ s₂ h
  cases s₁
  case s1 =>
    cases s₂
    case s2 => contradiction
    case s1 =>
      apply And.intro
      intro s₁'
      cases s₁'
      case left.s1 =>
        intro h₁
        contradiction
      case left.s2 =>
        intro h₁
        apply Exists.intro State.s2
        apply And.intro
        exact Transition.s1_to_s2
        rfl
        --The above three lines do the same thing as: "exact ⟨Transition.s1_to_s2 , rfl ⟩"
      case right =>
        intro s₂'
        cases s₂'
        case s1 =>
          intro h₁
          contradiction
        case s2 =>
          intro h₁
          apply Exists.intro State.s2
          exact ⟨Transition.s1_to_s2 , rfl⟩
          -- attempt for 1
    case s2 =>
      apply And.intro
      case left =>
        intro s₁' h₁
        cases h₁
        case s1_to_s2 =>
          apply Exists.intro State.s2
          apply And.intro
          case left => exact Transition.s1_to_s2
          case right => rfl
        case s2_to_s1 =>
          apply Exists.intro State.s1
          apply And.intro
          case left => exact Transition.s2_to_s1
          case right => rfl
      case right =>
        intro s₂'
        cases s₂'
        case s1 =>
          intro h₁
          contradiction
        case s2 =>
          intro h₁
          apply Exists.intro State.s2
          exact ⟨Transition.s1_to_s2, rfl⟩
    -- Exercise 1: try to complete on your own




-- Execrcise 2 : Complete the more general version

theorem bisimulation_proof_general {StateSpace : Type} {T : Type} (R : StateSpace → StateSpace → Prop) (TransitionFunction : StateSpace → StateSpace → Prop) : Prop :=
  ∀ (s₁ s₂ : StateSpace),
    R s₁ s₂ →
    (∀ (s₁' : StateSpace),
      TransitionFunction s₁ s₁' →
      ∃ (s₂' : StateSpace),
        TransitionFunction s₂ s₂' ∧ R s₁' s₂') ∧
    ∀ (s₂' : StateSpace),
      TransitionFunction s₂ s₂' →
      ∃ (s₁' : StateSpace),
        TransitionFunction s₁ s₁' ∧ R s₁' s₂'


-- Exercise 3: State ->  P(State) --- the one we have right now
--          Define bisimulation for transition systems of the following type:  State -> ℕ × State


def PState := State → Prop

def bisimulation_PState (R : PState → PState → Prop) : Prop :=
  ∀ (s₁ s₂ : State),
    R (λ x, x = s₁) (λ x, x = s₂) →
    (∀ (s₁' : State),
      Transition s₁ s₁' →
      ∃ (s₂' : State),
        Transition s₂ s₂' ∧ R (λ x, x = s₁') (λ x, x = s₂')) ∧
    ∀ (s₂' : State),
      Transition s₂ s₂' →
      ∃ (s₁' : State),
        Transition s₁ s₁' ∧ R (λ x, x = s₁') (λ x, x = s₂')
