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
    (∀ (s₁' : StateSpace),
      TransitionFunction s₁ s₁' →
      ∃ (s₂' : StateSpace),
        TransitionFunction s₂ s₂' ∧ R s₁' s₂') ∧
    ∀ (s₂' : StateSpace),
      TransitionFunction s₂ s₂' →
      ∃ (s₁' : StateSpace),
        TransitionFunction s₁ s₁' ∧ R s₁' s₂'


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
      case s2_to_s1 =>
        apply Exists.intro State.s1
        apply And.intro
        case left =>
          cases s₂
          case s1 => contradiction
          case s2 => exact Transition.s2_to_s1
        case right => rfl
    case right =>
      intro s₂' h1
      cases h1
      case s1_to_s2 =>
        apply Exists.intro State.s1
        apply And.intro
        case left =>
          exact Transition.s2_to_s1
        case right =>
          contradiction
      case s2_to_s1 =>
        apply Exists.intro State.s1
        apply And.intro
        case left =>
          exact Transition.s2_to_s1
        case right =>
          rfl


    -- Exercise 1: try to complete on your own




-- Execrcise 2 : Complete the more general version

theorem bisimulation_proof_general {StateSpace : Type} (R : StateSpace → StateSpace → Prop) (TransitionFunction : StateSpace → StateSpace → Prop) : Prop :=
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



def transition_function : State → Nat × State :=
  λ (s : State) => match s with
                  | State.s1 => ( 1 , State.s2)
                  | State.s2 => ( 1 , State.s1)


def bisimulation_of_stream_systems (R : State × State → Prop) : Prop :=
  ∀ (s₁ s₂ : State),
    R (s₁ , s₂) →
      let (output1, next1) := transition_function (s₁);
      let (output2, next2) := transition_function (s₂);
        output1 = output2 ∧ R (next1 , next2)


def bisim2 : (State × State → Prop) :=
  λ ((s₁ , s₂ ) : State × State) => s₁ = s₂

theorem bisim_proof_2 : bisimulation_of_stream_systems bisim2 := by
  intro s₁ s₂
  intro assume_related
  cases s₁
  all_goals (cases s₂)
  case s1.s2 =>
    contradiction
  case s2.s1 =>
    contradiction
  case s1.s1 =>
    apply And.intro
    case left =>
      rfl
    case right =>
      rfl
  case s2.s2 =>
    apply And.intro
    all_goals rfl

-- Exercise1: Make transitition systems generic in state spaace and transition funciton


theorem bisimulation_generic : is_bisimulation2 State Transition R := by
  intro s₁ s₂ h
  apply And.intro
  case left =>
    intro s₁' h₁
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
    intro s₂' h₂
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

-- Exercise 2: Make bisimulation generic

theorem bisimulation_exercise2 {StateSpace : Type} (R : StateSpace → StateSpace → Prop)
  (TransitionFunction : StateSpace → StateSpace → Prop) : Prop :=
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


-- Exercise 3: Try reporoving bisimulation for the concrete transition system on the state space State and for transition function "transition_function"
-- all i did was apply theorms, and went case by case and continued applying, i really wasn't sure how to approach this.

def nondeterministic_transition_function : State → State → Prop := by
  intro s
  intro t
  cases s
  case s1 =>
    cases t
    case s1 =>
      exact False
    case s2 =>
      exact True
  case s2 =>
    cases t
    case s1 =>
      exact True
    case s2 =>
      exact False


theorem bisimulation_exercise3 : is_bisimulation2 State (nondeterministic_transition_function) R := by
  intro s₁ s₂ h
  apply And.intro
  case left =>
    intro s₁' t₁
    cases s₁
    case s1 =>
      cases s₁'
      case s1 =>
        contradiction
      case s2 =>
        apply Exists.intro State.s2
        cases s₂
        case s1 =>
          apply And.intro
          exact t₁
          rfl
        case s2 =>
          contradiction
    case s2 =>
      cases s₂
      case s1 =>
        contradiction
      case s2 =>
        cases s₁'
        case s2 =>
          contradiction
        case s1 =>
          apply Exists.intro State.s1
          apply And.intro
          exact t₁
          rfl
  case right =>
    intro s₂' t₂
    cases s₁
    case s1 =>
      cases s₂
      case s2 =>
        contradiction
      case s1 =>
        cases s₂'
        case s1 => contradiction
        case s2 =>
          apply Exists.intro State.s2
          apply And.intro
          exact t₂
          rfl
    case s2 =>
      cases s₂
      case s1 =>
        contradiction
      case s2 =>
        cases s₂'
        case s2 =>
          contradiction
        case s1 =>
          apply Exists.intro State.s1
          apply And.intro
          exact t₂
          rfl


-- Exiercise 4(*) - Go intro Rutten notes, find some stream systems he shows is bisimiliar and implement it and prove the bisimilarity using Lean


-- streams :: N ----> N
-- head (stream) := stream 0
-- tail (stream) := lambda n ===> stream (n+1)

-- (s) --> (n, s')
-- (stream) --> (head stream, tail stream)

-- Exercise 1 : Define generic bisimulation of stream systems -- in particular make : "bisimulation_of_stream_systems" generic in type of transition function and state space
-- Exercise 2 : Recall the code you had for streams and equip the set of all streams with the structure of the transition system
-- (stream) --> (head stream, tail stream)
